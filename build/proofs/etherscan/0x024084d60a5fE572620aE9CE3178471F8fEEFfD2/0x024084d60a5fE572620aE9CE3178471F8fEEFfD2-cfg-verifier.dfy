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
      var s7 := Push2(s6, 0x0010);
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
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x10
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10 as nat
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
      var s6 := Push2(s5, 0x0088);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s631(s7, gas - 1)
      else
        ExecuteFromCFGNode_s3(s7, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x1a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a as nat
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
      var s6 := Push4(s5, 0x9d23d9f2);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x005b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s425(s9, gas - 1)
      else
        ExecuteFromCFGNode_s4(s9, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x9d23d9f2);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0101);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s290(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xabfd5310);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0131);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xb3596f07);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x014d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x017d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0088);
      assert s1.Peek(0) == 0x88;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s2, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 10
    * Segment Id for this node is: 37
    * Starting at 0x17d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0197);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0192);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x192;
      assert s11.Peek(3) == 0x197;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d4c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s14, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 221
    * Starting at 0xd4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x192

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x192;
      assert s1.Peek(3) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d62);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s10, gas - 1)
      else
        ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 222
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x192

    requires s0.stack[4] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d61);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0x192;
      assert s1.Peek(5) == 0x197;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s3, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xd61

    requires s0.stack[4] == 0x192

    requires s0.stack[5] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0x192;
      assert s1.Peek(5) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 14
    * Segment Id for this node is: 224
    * Starting at 0xd62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x192

    requires s0.stack[4] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x192;
      assert s1.Peek(4) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d70);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b05);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s9, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd70

    requires s0.stack[7] == 0x192

    requires s0.stack[8] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd70;
      assert s1.Peek(7) == 0x192;
      assert s1.Peek(8) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s10, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x192

    requires s0.stack[11] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0x192;
      assert s1.Peek(11) == 0x197;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xd70

    requires s0.stack[12] == 0x192

    requires s0.stack[13] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xd70;
      assert s1.Peek(12) == 0x192;
      assert s1.Peek(13) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s6, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xd70

    requires s0.stack[15] == 0x192

    requires s0.stack[16] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xd70;
      assert s1.Peek(15) == 0x192;
      assert s1.Peek(16) == 0x197;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s19(s11, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xd70

    requires s0.stack[14] == 0x192

    requires s0.stack[15] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xd70;
      assert s1.Peek(14) == 0x192;
      assert s1.Peek(15) == 0x197;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xd70

    requires s0.stack[11] == 0x192

    requires s0.stack[12] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0x192;
      assert s1.Peek(12) == 0x197;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s5, gas - 1)
      else
        ExecuteFromCFGNode_s21(s5, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x192

    requires s0.stack[11] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0x192;
      assert s1.Peek(12) == 0x197;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x192

    requires s0.stack[11] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0x192;
      assert s1.Peek(11) == 0x197;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd70

    requires s0.stack[8] == 0x192

    requires s0.stack[9] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd70;
      assert s1.Peek(8) == 0x192;
      assert s1.Peek(9) == 0x197;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s6, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 225
    * Starting at 0xd70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x192

    requires s0.stack[6] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x192;
      assert s1.Peek(6) == 0x197;
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
    * Segment Id for this node is: 38
    * Starting at 0x192
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x192 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x197;
      var s2 := Push2(s1, 0x051b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s3, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 79
    * Starting at 0x51b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x197;
      var s2 := Push2(s1, 0x0523);
      var s3 := Push2(s2, 0x05a1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s4, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 85
    * Starting at 0x5a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x523

    requires s0.stack[2] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x523;
      assert s1.Peek(2) == 0x197;
      var s2 := Push2(s1, 0x05a9);
      var s3 := Push2(s2, 0x09de);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s4, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x5a9

    requires s0.stack[1] == 0x523

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a9;
      assert s1.Peek(1) == 0x523;
      assert s1.Peek(3) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s7, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 86
    * Starting at 0x5a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x523

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x523;
      assert s1.Peek(3) == 0x197;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x05c7);
      var s5 := Push2(s4, 0x01c3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 46
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5c7

    requires s0.stack[2] == 0x523

    requires s0.stack[4] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c7;
      assert s1.Peek(2) == 0x523;
      assert s1.Peek(4) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x5c7;
      assert s11.Peek(4) == 0x523;
      assert s11.Peek(6) == 0x197;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s17, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 87
    * Starting at 0x5c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x523

    requires s0.stack[4] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x523;
      assert s1.Peek(4) == 0x197;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0626);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s6, gas - 1)
      else
        ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 88
    * Starting at 0x5e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x523

    requires s0.stack[2] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05ea);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x523;
      assert s1.Peek(3) == 0x197;
      var s2 := Push2(s1, 0x09de);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s3, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x5ea

    requires s0.stack[1] == 0x523

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x523;
      assert s1.Peek(3) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s7, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 89
    * Starting at 0x5ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x523

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x523;
      assert s1.Peek(3) == 0x197;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x061d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x61d;
      assert s11.Peek(3) == 0x523;
      assert s11.Peek(5) == 0x197;
      var s12 := Push2(s11, 0x0d31);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s13, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x61d

    requires s0.stack[3] == 0x523

    requires s0.stack[5] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x61d;
      assert s1.Peek(3) == 0x523;
      assert s1.Peek(5) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0x61d;
      assert s11.Peek(6) == 0x523;
      assert s11.Peek(8) == 0x197;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s14, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0x61d

    requires s0.stack[7] == 0x523

    requires s0.stack[9] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0x61d;
      assert s1.Peek(7) == 0x523;
      assert s1.Peek(9) == 0x197;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s5, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0x61d

    requires s0.stack[9] == 0x523

    requires s0.stack[11] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0x61d;
      assert s1.Peek(9) == 0x523;
      assert s1.Peek(11) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s6, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0x61d

    requires s0.stack[12] == 0x523

    requires s0.stack[14] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0x61d;
      assert s1.Peek(12) == 0x523;
      assert s1.Peek(14) == 0x197;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s39(s11, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0x61d

    requires s0.stack[11] == 0x523

    requires s0.stack[13] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0x61d;
      assert s1.Peek(11) == 0x523;
      assert s1.Peek(13) == 0x197;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0x61d

    requires s0.stack[8] == 0x523

    requires s0.stack[10] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0x61d;
      assert s1.Peek(8) == 0x523;
      assert s1.Peek(10) == 0x197;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s6, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x61d

    requires s0.stack[4] == 0x523

    requires s0.stack[6] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61d;
      assert s1.Peek(4) == 0x523;
      assert s1.Peek(6) == 0x197;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s6, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 90
    * Starting at 0x61d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x523

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x523;
      assert s1.Peek(3) == 0x197;
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
    * Segment Id for this node is: 91
    * Starting at 0x626
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x626 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x523

    requires s0.stack[2] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x523;
      assert s1.Peek(2) == 0x197;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s2, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 80
    * Starting at 0x523
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0595);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s10, gas - 1)
      else
        ExecuteFromCFGNode_s45(s10, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 81
    * Starting at 0x558
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x558 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x197;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x1e4fbdf700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x058c);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x58c;
      assert s11.Peek(4) == 0x197;
      var s12 := Push2(s11, 0x0d31);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s13, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x58c

    requires s0.stack[4] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x58c;
      assert s1.Peek(4) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0x58c;
      assert s11.Peek(7) == 0x197;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s14, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0x58c

    requires s0.stack[8] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0x58c;
      assert s1.Peek(8) == 0x197;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s5, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0x58c

    requires s0.stack[10] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0x58c;
      assert s1.Peek(10) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s6, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0x58c

    requires s0.stack[13] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0x58c;
      assert s1.Peek(13) == 0x197;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s50(s11, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0x58c

    requires s0.stack[12] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0x58c;
      assert s1.Peek(12) == 0x197;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s7, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0x58c

    requires s0.stack[9] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0x58c;
      assert s1.Peek(9) == 0x197;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x58c

    requires s0.stack[5] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x58c;
      assert s1.Peek(5) == 0x197;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s6, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 82
    * Starting at 0x58c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x197;
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

  /** Node 54
    * Segment Id for this node is: 83
    * Starting at 0x595
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x595 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x197;
      var s2 := Push2(s1, 0x059e);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0784);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s5, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 112
    * Starting at 0x784
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x59e

    requires s0.stack[3] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x59e;
      assert s1.Peek(3) == 0x197;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x59e;
      assert s11.Peek(5) == 0x197;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup1(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x59e;
      assert s21.Peek(8) == 0x197;
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
      assert s31.Peek(7) == 0x59e;
      assert s31.Peek(9) == 0x197;
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
      ExecuteFromCFGNode_s56(s41, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 113
    * Starting at 0x818
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x818 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x59e

    requires s0.stack[7] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x59e;
      assert s1.Peek(6) == 0x197;
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
      assert s11.Peek(2) == 0x59e;
      assert s11.Peek(4) == 0x197;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s14, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 84
    * Starting at 0x59e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x197

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x197;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s3, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 39
    * Starting at 0x197
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x197 as nat
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

  /** Node 59
    * Segment Id for this node is: 33
    * Starting at 0x14d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0167);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0162);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x162;
      assert s11.Peek(3) == 0x167;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d4c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s14, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 221
    * Starting at 0xd4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x162

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x162;
      assert s1.Peek(3) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d62);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s10, gas - 1)
      else
        ExecuteFromCFGNode_s61(s10, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 222
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x162

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d61);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0x162;
      assert s1.Peek(5) == 0x167;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s3, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xd61

    requires s0.stack[4] == 0x162

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0x162;
      assert s1.Peek(5) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 63
    * Segment Id for this node is: 224
    * Starting at 0xd62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x162

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x162;
      assert s1.Peek(4) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d70);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b05);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s9, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd70

    requires s0.stack[7] == 0x162

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd70;
      assert s1.Peek(7) == 0x162;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s10, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x162

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0x162;
      assert s1.Peek(11) == 0x167;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s5, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xd70

    requires s0.stack[12] == 0x162

    requires s0.stack[13] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xd70;
      assert s1.Peek(12) == 0x162;
      assert s1.Peek(13) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s6, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xd70

    requires s0.stack[15] == 0x162

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xd70;
      assert s1.Peek(15) == 0x162;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s68(s11, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xd70

    requires s0.stack[14] == 0x162

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xd70;
      assert s1.Peek(14) == 0x162;
      assert s1.Peek(15) == 0x167;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xd70

    requires s0.stack[11] == 0x162

    requires s0.stack[12] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0x162;
      assert s1.Peek(12) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s5, gas - 1)
      else
        ExecuteFromCFGNode_s70(s5, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x162

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0x162;
      assert s1.Peek(12) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 71
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x162

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0x162;
      assert s1.Peek(11) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s3, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd70

    requires s0.stack[8] == 0x162

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd70;
      assert s1.Peek(8) == 0x162;
      assert s1.Peek(9) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s6, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 225
    * Starting at 0xd70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x162

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x162;
      assert s1.Peek(6) == 0x167;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s9, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 34
    * Starting at 0x162
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x167;
      var s2 := Push2(s1, 0x0332);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s3, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 68
    * Starting at 0x332
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x332 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup5(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Push20(s8, 0xffffffffffffffffffffffffffffffffffffffff);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x167;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x00);
      var s21 := Keccak256(s20);
      assert s21.Peek(4) == 0x167;
      var s22 := Push1(s21, 0x00);
      var s23 := Swap1(s22);
      var s24 := SLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push2(s25, 0x0100);
      var s27 := Exp(s26);
      var s28 := Swap1(s27);
      var s29 := Div(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(4) == 0x167;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      var s35 := Push20(s34, 0xffffffffffffffffffffffffffffffffffffffff);
      var s36 := And(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Eq(s39);
      var s41 := Push2(s40, 0x044c);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s41, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 69
    * Starting at 0x3cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x44c

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpI(s0);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s0.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s1, gas - 1)
      else
        ExecuteFromCFGNode_s77(s1, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 70
    * Starting at 0x3cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push4(s4, 0xfeaf968c);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Push4(s8, 0xffffffff);
      var s10 := And(s9);
      var s11 := Push1(s10, 0xe0);
      assert s11.Peek(9) == 0x167;
      var s12 := Shl(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0xa0);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(11) == 0x167;
      var s22 := Sub(s21);
      var s23 := Dup2(s22);
      var s24 := Dup7(s23);
      var s25 := Gas(s24);
      var s26 := StaticCall(s25);
      var s27 := IsZero(s26);
      var s28 := Dup1(s27);
      var s29 := IsZero(s28);
      var s30 := Push2(s29, 0x0418);
      var s31 := JumpI(s30);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s30.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s31, gas - 1)
      else
        ExecuteFromCFGNode_s78(s31, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 71
    * Starting at 0x40f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 79
    * Segment Id for this node is: 72
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x167;
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
      assert s11.Peek(8) == 0x167;
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
      assert s21.Peek(7) == 0x167;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x043c);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x105f);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s28, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 297
    * Starting at 0x105f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x43c

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x43c;
      assert s1.Peek(7) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Push1(s6, 0xa0);
      var s8 := Dup7(s7);
      var s9 := Dup9(s8);
      var s10 := Sub(s9);
      var s11 := SLt(s10);
      assert s11.Peek(8) == 0x43c;
      assert s11.Peek(13) == 0x167;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x107b);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s14, gas - 1)
      else
        ExecuteFromCFGNode_s81(s14, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 298
    * Starting at 0x1073
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1073 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x43c

    requires s0.stack[12] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x107a);
      assert s1.Peek(0) == 0x107a;
      assert s1.Peek(8) == 0x43c;
      assert s1.Peek(13) == 0x167;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s3, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x107a

    requires s0.stack[8] == 0x43c

    requires s0.stack[13] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x107a;
      assert s1.Peek(8) == 0x43c;
      assert s1.Peek(13) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 83
    * Segment Id for this node is: 300
    * Starting at 0x107b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x43c

    requires s0.stack[12] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x43c;
      assert s1.Peek(12) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1089);
      var s4 := Dup9(s3);
      var s5 := Dup3(s4);
      var s6 := Dup10(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0fff);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s9, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 286
    * Starting at 0xfff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1089

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1089;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x100e);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fe8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s10, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 282
    * Starting at 0xfe8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x1089

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x1089;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Push2(s1, 0x0ff1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fd2);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s5, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 281
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xff1

    requires s0.stack[3] == 0x100e

    requires s0.stack[7] == 0x1089

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xff1;
      assert s1.Peek(3) == 0x100e;
      assert s1.Peek(7) == 0x1089;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := PushN(s2, 10, 0xffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s11, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 283
    * Starting at 0xff1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x100e

    requires s0.stack[6] == 0x1089

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x1089;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ffc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s5, gas - 1)
      else
        ExecuteFromCFGNode_s88(s5, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 284
    * Starting at 0xff8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x1089

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x1089;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 89
    * Segment Id for this node is: 285
    * Starting at 0xffc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x1089

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x1089;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s3, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 287
    * Starting at 0x100e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x1089

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1089;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s6, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 301
    * Starting at 0x1089
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1089 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x167;
      var s2 := Swap6(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x109a);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x1035);
      assert s11.Peek(0) == 0x1035;
      assert s11.Peek(3) == 0x109a;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x167;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s12, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 293
    * Starting at 0x1035
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x109a

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109a;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x101e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s10, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 289
    * Starting at 0x101e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1044

    requires s0.stack[5] == 0x109a

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1044;
      assert s1.Peek(5) == 0x109a;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Push2(s1, 0x1027);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1014);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s5, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 288
    * Starting at 0x1014
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1014 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0x1027

    requires s0.stack[3] == 0x1044

    requires s0.stack[7] == 0x109a

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1027;
      assert s1.Peek(3) == 0x1044;
      assert s1.Peek(7) == 0x109a;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s9, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 290
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1044

    requires s0.stack[6] == 0x109a

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1044;
      assert s1.Peek(6) == 0x109a;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1032);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s5, gas - 1)
      else
        ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 291
    * Starting at 0x102e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1044

    requires s0.stack[5] == 0x109a

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1044;
      assert s1.Peek(6) == 0x109a;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 97
    * Segment Id for this node is: 292
    * Starting at 0x1032
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1032 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1044

    requires s0.stack[5] == 0x109a

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1044;
      assert s1.Peek(5) == 0x109a;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 294
    * Starting at 0x1044
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x109a

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x109a;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s6, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 302
    * Starting at 0x109a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x167;
      var s2 := Swap5(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x10ab);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x104a);
      assert s11.Peek(0) == 0x104a;
      assert s11.Peek(3) == 0x10ab;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x167;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s12, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 295
    * Starting at 0x104a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x10ab

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ab;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x1059);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0be7);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s10, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 184
    * Starting at 0xbe7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10ab

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10ab;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Push2(s1, 0x0bf0);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s5, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xbf0

    requires s0.stack[3] == 0x1059

    requires s0.stack[7] == 0x10ab

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbf0;
      assert s1.Peek(3) == 0x1059;
      assert s1.Peek(7) == 0x10ab;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s9, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 185
    * Starting at 0xbf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1059

    requires s0.stack[6] == 0x10ab

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10ab;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s5, gas - 1)
      else
        ExecuteFromCFGNode_s104(s5, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 186
    * Starting at 0xbf7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10ab

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10ab;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 105
    * Segment Id for this node is: 187
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10ab

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10ab;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 296
    * Starting at 0x1059
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1059 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x10ab

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10ab;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s6, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 303
    * Starting at 0x10ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x167;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Push2(s5, 0x10bc);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x104a);
      assert s11.Peek(0) == 0x104a;
      assert s11.Peek(3) == 0x10bc;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x167;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s12, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 295
    * Starting at 0x104a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x10bc

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10bc;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x1059);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0be7);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s10, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 184
    * Starting at 0xbe7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10bc

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10bc;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Push2(s1, 0x0bf0);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s5, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xbf0

    requires s0.stack[3] == 0x1059

    requires s0.stack[7] == 0x10bc

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbf0;
      assert s1.Peek(3) == 0x1059;
      assert s1.Peek(7) == 0x10bc;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s9, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 185
    * Starting at 0xbf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1059

    requires s0.stack[6] == 0x10bc

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10bc;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s5, gas - 1)
      else
        ExecuteFromCFGNode_s112(s5, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 186
    * Starting at 0xbf7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10bc

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10bc;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 113
    * Segment Id for this node is: 187
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10bc

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10bc;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s3, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 296
    * Starting at 0x1059
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1059 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x10bc

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10bc;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s6, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 304
    * Starting at 0x10bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x80);
      var s6 := Push2(s5, 0x10cd);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0fff);
      assert s11.Peek(0) == 0xfff;
      assert s11.Peek(3) == 0x10cd;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x167;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s12, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 286
    * Starting at 0xfff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x10cd

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10cd;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x100e);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fe8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s10, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 282
    * Starting at 0xfe8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x10cd

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x10cd;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Push2(s1, 0x0ff1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fd2);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s5, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 281
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xff1

    requires s0.stack[3] == 0x100e

    requires s0.stack[7] == 0x10cd

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xff1;
      assert s1.Peek(3) == 0x100e;
      assert s1.Peek(7) == 0x10cd;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := PushN(s2, 10, 0xffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s11, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 283
    * Starting at 0xff1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x100e

    requires s0.stack[6] == 0x10cd

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x10cd;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ffc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s5, gas - 1)
      else
        ExecuteFromCFGNode_s120(s5, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 284
    * Starting at 0xff8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x10cd

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x10cd;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 121
    * Segment Id for this node is: 285
    * Starting at 0xffc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x10cd

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x10cd;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s3, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 287
    * Starting at 0x100e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x10cd

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10cd;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 305
    * Starting at 0x10cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x167;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap6(s8);
      var s10 := Swap1(s9);
      var s11 := Swap4(s10);
      assert s11.Peek(1) == 0x43c;
      assert s11.Peek(11) == 0x167;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s13, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 73
    * Starting at 0x43c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x167;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Dup1(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0x167;
      var s12 := Pop(s11);
      var s13 := Push2(s12, 0x0516);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s14, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 78
    * Starting at 0x516
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x516 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x167;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s5, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 35
    * Starting at 0x167
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x0174);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0f88);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s8, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 278
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x174

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x174;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0f9d);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xf9d;
      assert s11.Peek(5) == 0x174;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0f79);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s14, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 276
    * Starting at 0xf79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xf9d

    requires s0.stack[6] == 0x174

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9d;
      assert s1.Peek(6) == 0x174;
      var s2 := Push2(s1, 0x0f82);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s5, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf82

    requires s0.stack[4] == 0xf9d

    requires s0.stack[8] == 0x174

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf82;
      assert s1.Peek(4) == 0xf9d;
      assert s1.Peek(8) == 0x174;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s9, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 277
    * Starting at 0xf82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xf9d

    requires s0.stack[7] == 0x174

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9d;
      assert s1.Peek(7) == 0x174;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s6, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 279
    * Starting at 0xf9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x174

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x174;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s6, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 36
    * Starting at 0x174
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x174 as nat
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

  /** Node 133
    * Segment Id for this node is: 74
    * Starting at 0x44c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x167;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x167;
      var s22 := Eq(s21);
      var s23 := Push2(s22, 0x04db);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s24, gas - 1)
      else
        ExecuteFromCFGNode_s134(s24, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 75
    * Starting at 0x494
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x494 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(4) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup5(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x167;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(3) == 0x167;
      var s22 := Pop(s21);
      var s23 := Push2(s22, 0x0516);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s24, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 76
    * Starting at 0x4db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x167;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x050d);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x1137);
      assert s11.Peek(0) == 0x1137;
      assert s11.Peek(2) == 0x50d;
      assert s11.Peek(6) == 0x167;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s12, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 311
    * Starting at 0x1137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x50d

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x50d;
      assert s1.Peek(5) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x50d;
      assert s11.Peek(8) == 0x167;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1150);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1114);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s18, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 308
    * Starting at 0x1114
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1150

    requires s0.stack[4] == 0x50d

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1150;
      assert s1.Peek(4) == 0x50d;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1121);
      var s4 := Push1(s3, 0x0f);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x10da);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s7, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 306
    * Starting at 0x10da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x1121

    requires s0.stack[5] == 0x1150

    requires s0.stack[8] == 0x50d

    requires s0.stack[12] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1121;
      assert s1.Peek(5) == 0x1150;
      assert s1.Peek(8) == 0x50d;
      assert s1.Peek(12) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1121;
      assert s11.Peek(6) == 0x1150;
      assert s11.Peek(9) == 0x50d;
      assert s11.Peek(13) == 0x167;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s15, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 309
    * Starting at 0x1121
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1150

    requires s0.stack[6] == 0x50d

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1150;
      assert s1.Peek(6) == 0x50d;
      assert s1.Peek(10) == 0x167;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x112c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x10eb);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s7, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 307
    * Starting at 0x10eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x112c

    requires s0.stack[4] == 0x1150

    requires s0.stack[7] == 0x50d

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x112c;
      assert s1.Peek(4) == 0x1150;
      assert s1.Peek(7) == 0x50d;
      assert s1.Peek(11) == 0x167;
      var s2 := Push32(s1, 0x6173736574206e6f7420666f756e640000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s8, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 310
    * Starting at 0x112c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1150

    requires s0.stack[5] == 0x50d

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1150;
      assert s1.Peek(5) == 0x50d;
      assert s1.Peek(9) == 0x167;
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
      ExecuteFromCFGNode_s142(s10, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 312
    * Starting at 0x1150
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x50d

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50d;
      assert s1.Peek(7) == 0x167;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s7, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 77
    * Starting at 0x50d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x167;
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

  /** Node 144
    * Segment Id for this node is: 30
    * Starting at 0x131
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x014b);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0146);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x146;
      assert s11.Peek(3) == 0x14b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f01);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s14, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 264
    * Starting at 0xf01
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x146

    requires s0.stack[3] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x146;
      assert s1.Peek(3) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f18);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s11, gas - 1)
      else
        ExecuteFromCFGNode_s146(s11, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 265
    * Starting at 0xf10
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x146

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f17);
      assert s1.Peek(0) == 0xf17;
      assert s1.Peek(5) == 0x146;
      assert s1.Peek(6) == 0x14b;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s3, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xf17

    requires s0.stack[5] == 0x146

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf17;
      assert s1.Peek(5) == 0x146;
      assert s1.Peek(6) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 148
    * Segment Id for this node is: 267
    * Starting at 0xf18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x146

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x146;
      assert s1.Peek(5) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f36);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s11, gas - 1)
      else
        ExecuteFromCFGNode_s149(s11, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 268
    * Starting at 0xf2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x146

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f35);
      assert s1.Peek(0) == 0xf35;
      assert s1.Peek(6) == 0x146;
      assert s1.Peek(7) == 0x14b;
      var s2 := Push2(s1, 0x09f5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s3, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 138
    * Starting at 0x9f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xf35

    requires s0.stack[6] == 0x146

    requires s0.stack[7] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf35;
      assert s1.Peek(6) == 0x146;
      assert s1.Peek(7) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 151
    * Segment Id for this node is: 270
    * Starting at 0xf36
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x146

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x146;
      assert s1.Peek(6) == 0x14b;
      var s2 := Push2(s1, 0x0f42);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0b83);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s8, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 174
    * Starting at 0xb83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf42

    requires s0.stack[8] == 0x146

    requires s0.stack[9] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf42;
      assert s1.Peek(8) == 0x146;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0b98);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s9, gas - 1)
      else
        ExecuteFromCFGNode_s153(s9, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 175
    * Starting at 0xb90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf42

    requires s0.stack[9] == 0x146

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b97);
      assert s1.Peek(0) == 0xb97;
      assert s1.Peek(4) == 0xf42;
      assert s1.Peek(10) == 0x146;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push2(s1, 0x09fa);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s3, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 139
    * Starting at 0x9fa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xb97

    requires s0.stack[4] == 0xf42

    requires s0.stack[10] == 0x146

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb97;
      assert s1.Peek(4) == 0xf42;
      assert s1.Peek(10) == 0x146;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 155
    * Segment Id for this node is: 177
    * Starting at 0xb98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf42

    requires s0.stack[9] == 0x146

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf42;
      assert s1.Peek(9) == 0x146;
      assert s1.Peek(10) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0ba8);
      var s5 := Dup5(s4);
      var s6 := Dup3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0b1a);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s11, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 164
    * Starting at 0xb1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xba8

    requires s0.stack[8] == 0xf42

    requires s0.stack[14] == 0x146

    requires s0.stack[15] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xba8;
      assert s1.Peek(8) == 0xf42;
      assert s1.Peek(14) == 0x146;
      assert s1.Peek(15) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0b2d);
      var s4 := Push2(s3, 0x0b28);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0a8b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s7, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 150
    * Starting at 0xa8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xb28

    requires s0.stack[2] == 0xb2d

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf42

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb28;
      assert s1.Peek(2) == 0xb2d;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf42;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0aa6);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s8, gas - 1)
      else
        ExecuteFromCFGNode_s158(s8, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 151
    * Starting at 0xa9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xb28

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf42

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0aa5);
      assert s1.Peek(0) == 0xaa5;
      assert s1.Peek(3) == 0xb28;
      assert s1.Peek(4) == 0xb2d;
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xf42;
      assert s1.Peek(20) == 0x146;
      assert s1.Peek(21) == 0x14b;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s3, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xaa5

    requires s0.stack[3] == 0xb28

    requires s0.stack[4] == 0xb2d

    requires s0.stack[9] == 0xba8

    requires s0.stack[14] == 0xf42

    requires s0.stack[20] == 0x146

    requires s0.stack[21] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xaa5;
      assert s1.Peek(3) == 0xb28;
      assert s1.Peek(4) == 0xb2d;
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xf42;
      assert s1.Peek(20) == 0x146;
      assert s1.Peek(21) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 160
    * Segment Id for this node is: 153
    * Starting at 0xaa6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xb28

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf42

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb28;
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf42;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0xb28;
      assert s11.Peek(3) == 0xb2d;
      assert s11.Peek(8) == 0xba8;
      assert s11.Peek(13) == 0xf42;
      assert s11.Peek(19) == 0x146;
      assert s11.Peek(20) == 0x14b;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s15, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 165
    * Starting at 0xb28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xb2d

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf42

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2d;
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xf42;
      assert s1.Peek(17) == 0x146;
      assert s1.Peek(18) == 0x14b;
      var s2 := Push2(s1, 0x0a70);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s3, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 147
    * Starting at 0xa70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xb2d

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf42

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2d;
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xf42;
      assert s1.Peek(17) == 0x146;
      assert s1.Peek(18) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0a7a);
      var s4 := Push2(s3, 0x09e6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 136
    * Starting at 0x9e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xa7a

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf42

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa7a;
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf42;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s8, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 148
    * Starting at 0xa7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf42

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf42;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Push2(s6, 0x0a3f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s8, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 142
    * Starting at 0xa3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xa86

    requires s0.stack[5] == 0xb2d

    requires s0.stack[10] == 0xba8

    requires s0.stack[15] == 0xf42

    requires s0.stack[21] == 0x146

    requires s0.stack[22] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa86;
      assert s1.Peek(5) == 0xb2d;
      assert s1.Peek(10) == 0xba8;
      assert s1.Peek(15) == 0xf42;
      assert s1.Peek(21) == 0x146;
      assert s1.Peek(22) == 0x14b;
      var s2 := Push2(s1, 0x0a48);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09ff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s5, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 140
    * Starting at 0x9ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xa48

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xb2d

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xf42

    requires s0.stack[23] == 0x146

    requires s0.stack[24] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa48;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf42;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xa48;
      assert s11.Peek(5) == 0xa86;
      assert s11.Peek(8) == 0xb2d;
      assert s11.Peek(13) == 0xba8;
      assert s11.Peek(18) == 0xf42;
      assert s11.Peek(24) == 0x146;
      assert s11.Peek(25) == 0x14b;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s14, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 143
    * Starting at 0xa48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf42

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xb2d;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xf42;
      assert s1.Peek(22) == 0x146;
      assert s1.Peek(23) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := Or(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(4) == 0xa86;
      assert s11.Peek(7) == 0xb2d;
      assert s11.Peek(12) == 0xba8;
      assert s11.Peek(17) == 0xf42;
      assert s11.Peek(23) == 0x146;
      assert s11.Peek(24) == 0x14b;
      var s12 := Push2(s11, 0x0a67);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s13, gas - 1)
      else
        ExecuteFromCFGNode_s168(s13, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 144
    * Starting at 0xa5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf42

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a66);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf42;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s3, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[0] == 0xa66

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xb2d

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xf42

    requires s0.stack[23] == 0x146

    requires s0.stack[24] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf42;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 170
    * Segment Id for this node is: 146
    * Starting at 0xa67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf42

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xb2d;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xf42;
      assert s1.Peek(22) == 0x146;
      assert s1.Peek(23) == 0x14b;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s8, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 149
    * Starting at 0xa86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xb2d

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf42

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb2d;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf42;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s5, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 166
    * Starting at 0xb2d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xba8

    requires s0.stack[10] == 0xf42

    requires s0.stack[16] == 0x146

    requires s0.stack[17] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xba8;
      assert s1.Peek(10) == 0xf42;
      assert s1.Peek(16) == 0x146;
      assert s1.Peek(17) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0xba8;
      assert s11.Peek(11) == 0xf42;
      assert s11.Peek(17) == 0x146;
      assert s11.Peek(18) == 0x14b;
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup5(s13);
      var s15 := Mul(s14);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := Dup6(s17);
      var s19 := Dup2(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0xba8;
      assert s21.Peek(12) == 0xf42;
      assert s21.Peek(18) == 0x146;
      assert s21.Peek(19) == 0x14b;
      var s22 := Push2(s21, 0x0b50);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s23, gas - 1)
      else
        ExecuteFromCFGNode_s173(s23, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 167
    * Starting at 0xb48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf42

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b4f);
      assert s1.Peek(0) == 0xb4f;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf42;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Push2(s1, 0x0ab7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s3, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 154
    * Starting at 0xab7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xb4f

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf42

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb4f;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf42;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 175
    * Segment Id for this node is: 169
    * Starting at 0xb50
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf42

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xf42;
      assert s1.Peek(17) == 0x146;
      assert s1.Peek(18) == 0x14b;
      var s2 := Dup4(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s176(s2, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 170
    * Starting at 0xb52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf42

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf42;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b79);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s7, gas - 1)
      else
        ExecuteFromCFGNode_s177(s7, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 171
    * Starting at 0xb5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf42

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf42;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push2(s1, 0x0b65);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0b05);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xb65

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf42

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb65;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xf42;
      assert s1.Peek(22) == 0x146;
      assert s1.Peek(23) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s10, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xf42

    requires s0.stack[25] == 0x146

    requires s0.stack[26] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xb65;
      assert s1.Peek(14) == 0xba8;
      assert s1.Peek(19) == 0xf42;
      assert s1.Peek(25) == 0x146;
      assert s1.Peek(26) == 0x14b;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s5, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xb65

    requires s0.stack[16] == 0xba8

    requires s0.stack[21] == 0xf42

    requires s0.stack[27] == 0x146

    requires s0.stack[28] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xb65;
      assert s1.Peek(16) == 0xba8;
      assert s1.Peek(21) == 0xf42;
      assert s1.Peek(27) == 0x146;
      assert s1.Peek(28) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s6, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xb65

    requires s0.stack[19] == 0xba8

    requires s0.stack[24] == 0xf42

    requires s0.stack[30] == 0x146

    requires s0.stack[31] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xb65;
      assert s1.Peek(19) == 0xba8;
      assert s1.Peek(24) == 0xf42;
      assert s1.Peek(30) == 0x146;
      assert s1.Peek(31) == 0x14b;
      var s2 := Push1(s1, 0x00);
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
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xb65

    requires s0.stack[18] == 0xba8

    requires s0.stack[23] == 0xf42

    requires s0.stack[29] == 0x146

    requires s0.stack[30] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xb65;
      assert s1.Peek(18) == 0xba8;
      assert s1.Peek(23) == 0xf42;
      assert s1.Peek(29) == 0x146;
      assert s1.Peek(30) == 0x14b;
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
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xb65

    requires s0.stack[15] == 0xba8

    requires s0.stack[20] == 0xf42

    requires s0.stack[26] == 0x146

    requires s0.stack[27] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xb65;
      assert s1.Peek(15) == 0xba8;
      assert s1.Peek(20) == 0xf42;
      assert s1.Peek(26) == 0x146;
      assert s1.Peek(27) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s5, gas - 1)
      else
        ExecuteFromCFGNode_s184(s5, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xf42

    requires s0.stack[25] == 0x146

    requires s0.stack[26] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xb65;
      assert s1.Peek(15) == 0xba8;
      assert s1.Peek(20) == 0xf42;
      assert s1.Peek(26) == 0x146;
      assert s1.Peek(27) == 0x14b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 185
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xf42

    requires s0.stack[25] == 0x146

    requires s0.stack[26] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xb65;
      assert s1.Peek(14) == 0xba8;
      assert s1.Peek(19) == 0xf42;
      assert s1.Peek(25) == 0x146;
      assert s1.Peek(26) == 0x14b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xb65

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xf42

    requires s0.stack[23] == 0x146

    requires s0.stack[24] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb65;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf42;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s6, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 172
    * Starting at 0xb65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0xba8

    requires s0.stack[14] == 0xf42

    requires s0.stack[20] == 0x146

    requires s0.stack[21] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xf42;
      assert s1.Peek(20) == 0x146;
      assert s1.Peek(21) == 0x14b;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0xba8;
      assert s11.Peek(14) == 0xf42;
      assert s11.Peek(20) == 0x146;
      assert s11.Peek(21) == 0x14b;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0b52);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s16, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 173
    * Starting at 0xb79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf42

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf42;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s10, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 178
    * Starting at 0xba8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xf42

    requires s0.stack[11] == 0x146

    requires s0.stack[12] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf42;
      assert s1.Peek(11) == 0x146;
      assert s1.Peek(12) == 0x14b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s9, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 271
    * Starting at 0xf42
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x146

    requires s0.stack[7] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x146;
      assert s1.Peek(7) == 0x14b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push8(s8, 0xffffffffffffffff);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0x146;
      assert s11.Peek(7) == 0x14b;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0f63);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s14, gas - 1)
      else
        ExecuteFromCFGNode_s191(s14, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 272
    * Starting at 0xf5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x146

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f62);
      assert s1.Peek(0) == 0xf62;
      assert s1.Peek(6) == 0x146;
      assert s1.Peek(7) == 0x14b;
      var s2 := Push2(s1, 0x09f5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s3, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 138
    * Starting at 0x9f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xf62

    requires s0.stack[6] == 0x146

    requires s0.stack[7] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf62;
      assert s1.Peek(6) == 0x146;
      assert s1.Peek(7) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 193
    * Segment Id for this node is: 274
    * Starting at 0xf63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x146

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x146;
      assert s1.Peek(6) == 0x14b;
      var s2 := Push2(s1, 0x0f6f);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0b83);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s8, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 174
    * Starting at 0xb83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xf6f

    requires s0.stack[8] == 0x146

    requires s0.stack[9] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf6f;
      assert s1.Peek(8) == 0x146;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0b98);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s9, gas - 1)
      else
        ExecuteFromCFGNode_s195(s9, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 175
    * Starting at 0xb90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf6f

    requires s0.stack[9] == 0x146

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b97);
      assert s1.Peek(0) == 0xb97;
      assert s1.Peek(4) == 0xf6f;
      assert s1.Peek(10) == 0x146;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push2(s1, 0x09fa);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s3, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 139
    * Starting at 0x9fa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xb97

    requires s0.stack[4] == 0xf6f

    requires s0.stack[10] == 0x146

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb97;
      assert s1.Peek(4) == 0xf6f;
      assert s1.Peek(10) == 0x146;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 197
    * Segment Id for this node is: 177
    * Starting at 0xb98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xf6f

    requires s0.stack[9] == 0x146

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf6f;
      assert s1.Peek(9) == 0x146;
      assert s1.Peek(10) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0ba8);
      var s5 := Dup5(s4);
      var s6 := Dup3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0b1a);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s11, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 164
    * Starting at 0xb1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xba8

    requires s0.stack[8] == 0xf6f

    requires s0.stack[14] == 0x146

    requires s0.stack[15] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xba8;
      assert s1.Peek(8) == 0xf6f;
      assert s1.Peek(14) == 0x146;
      assert s1.Peek(15) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0b2d);
      var s4 := Push2(s3, 0x0b28);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0a8b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s7, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 150
    * Starting at 0xa8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xb28

    requires s0.stack[2] == 0xb2d

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf6f

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb28;
      assert s1.Peek(2) == 0xb2d;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf6f;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0aa6);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s8, gas - 1)
      else
        ExecuteFromCFGNode_s200(s8, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 151
    * Starting at 0xa9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xb28

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf6f

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0aa5);
      assert s1.Peek(0) == 0xaa5;
      assert s1.Peek(3) == 0xb28;
      assert s1.Peek(4) == 0xb2d;
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xf6f;
      assert s1.Peek(20) == 0x146;
      assert s1.Peek(21) == 0x14b;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s3, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xaa5

    requires s0.stack[3] == 0xb28

    requires s0.stack[4] == 0xb2d

    requires s0.stack[9] == 0xba8

    requires s0.stack[14] == 0xf6f

    requires s0.stack[20] == 0x146

    requires s0.stack[21] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xaa5;
      assert s1.Peek(3) == 0xb28;
      assert s1.Peek(4) == 0xb2d;
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xf6f;
      assert s1.Peek(20) == 0x146;
      assert s1.Peek(21) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 202
    * Segment Id for this node is: 153
    * Starting at 0xaa6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xb28

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf6f

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb28;
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf6f;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0xb28;
      assert s11.Peek(3) == 0xb2d;
      assert s11.Peek(8) == 0xba8;
      assert s11.Peek(13) == 0xf6f;
      assert s11.Peek(19) == 0x146;
      assert s11.Peek(20) == 0x14b;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s15, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 165
    * Starting at 0xb28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xb2d

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf6f

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2d;
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xf6f;
      assert s1.Peek(17) == 0x146;
      assert s1.Peek(18) == 0x14b;
      var s2 := Push2(s1, 0x0a70);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s3, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 147
    * Starting at 0xa70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xb2d

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf6f

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2d;
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xf6f;
      assert s1.Peek(17) == 0x146;
      assert s1.Peek(18) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0a7a);
      var s4 := Push2(s3, 0x09e6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s5, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 136
    * Starting at 0x9e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xa7a

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf6f

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa7a;
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf6f;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s8, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 148
    * Starting at 0xa7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xf6f

    requires s0.stack[19] == 0x146

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf6f;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Push2(s6, 0x0a3f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s8, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 142
    * Starting at 0xa3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xa86

    requires s0.stack[5] == 0xb2d

    requires s0.stack[10] == 0xba8

    requires s0.stack[15] == 0xf6f

    requires s0.stack[21] == 0x146

    requires s0.stack[22] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa86;
      assert s1.Peek(5) == 0xb2d;
      assert s1.Peek(10) == 0xba8;
      assert s1.Peek(15) == 0xf6f;
      assert s1.Peek(21) == 0x146;
      assert s1.Peek(22) == 0x14b;
      var s2 := Push2(s1, 0x0a48);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09ff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s5, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 140
    * Starting at 0x9ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xa48

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xb2d

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xf6f

    requires s0.stack[23] == 0x146

    requires s0.stack[24] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa48;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf6f;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xa48;
      assert s11.Peek(5) == 0xa86;
      assert s11.Peek(8) == 0xb2d;
      assert s11.Peek(13) == 0xba8;
      assert s11.Peek(18) == 0xf6f;
      assert s11.Peek(24) == 0x146;
      assert s11.Peek(25) == 0x14b;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s14, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 143
    * Starting at 0xa48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf6f

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xb2d;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xf6f;
      assert s1.Peek(22) == 0x146;
      assert s1.Peek(23) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := Or(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(4) == 0xa86;
      assert s11.Peek(7) == 0xb2d;
      assert s11.Peek(12) == 0xba8;
      assert s11.Peek(17) == 0xf6f;
      assert s11.Peek(23) == 0x146;
      assert s11.Peek(24) == 0x14b;
      var s12 := Push2(s11, 0x0a67);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s13, gas - 1)
      else
        ExecuteFromCFGNode_s210(s13, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 144
    * Starting at 0xa5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf6f

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a66);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf6f;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s3, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[0] == 0xa66

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xb2d

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xf6f

    requires s0.stack[23] == 0x146

    requires s0.stack[24] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf6f;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 212
    * Segment Id for this node is: 146
    * Starting at 0xa67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf6f

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xb2d;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xf6f;
      assert s1.Peek(22) == 0x146;
      assert s1.Peek(23) == 0x14b;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s8, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 149
    * Starting at 0xa86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xb2d

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf6f

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb2d;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf6f;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s5, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 166
    * Starting at 0xb2d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xba8

    requires s0.stack[10] == 0xf6f

    requires s0.stack[16] == 0x146

    requires s0.stack[17] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xba8;
      assert s1.Peek(10) == 0xf6f;
      assert s1.Peek(16) == 0x146;
      assert s1.Peek(17) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0xba8;
      assert s11.Peek(11) == 0xf6f;
      assert s11.Peek(17) == 0x146;
      assert s11.Peek(18) == 0x14b;
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup5(s13);
      var s15 := Mul(s14);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := Dup6(s17);
      var s19 := Dup2(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0xba8;
      assert s21.Peek(12) == 0xf6f;
      assert s21.Peek(18) == 0x146;
      assert s21.Peek(19) == 0x14b;
      var s22 := Push2(s21, 0x0b50);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s217(s23, gas - 1)
      else
        ExecuteFromCFGNode_s215(s23, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 167
    * Starting at 0xb48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf6f

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b4f);
      assert s1.Peek(0) == 0xb4f;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf6f;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Push2(s1, 0x0ab7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s3, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 154
    * Starting at 0xab7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xb4f

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf6f

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb4f;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf6f;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 217
    * Segment Id for this node is: 169
    * Starting at 0xb50
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xf6f

    requires s0.stack[17] == 0x146

    requires s0.stack[18] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xf6f;
      assert s1.Peek(17) == 0x146;
      assert s1.Peek(18) == 0x14b;
      var s2 := Dup4(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s218(s2, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 170
    * Starting at 0xb52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf6f

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf6f;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b79);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s7, gas - 1)
      else
        ExecuteFromCFGNode_s219(s7, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 171
    * Starting at 0xb5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf6f

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xf6f;
      assert s1.Peek(19) == 0x146;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push2(s1, 0x0b65);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0b05);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s6, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xb65

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xf6f

    requires s0.stack[22] == 0x146

    requires s0.stack[23] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb65;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xf6f;
      assert s1.Peek(22) == 0x146;
      assert s1.Peek(23) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s10, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xf6f

    requires s0.stack[25] == 0x146

    requires s0.stack[26] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xb65;
      assert s1.Peek(14) == 0xba8;
      assert s1.Peek(19) == 0xf6f;
      assert s1.Peek(25) == 0x146;
      assert s1.Peek(26) == 0x14b;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xb65

    requires s0.stack[16] == 0xba8

    requires s0.stack[21] == 0xf6f

    requires s0.stack[27] == 0x146

    requires s0.stack[28] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xb65;
      assert s1.Peek(16) == 0xba8;
      assert s1.Peek(21) == 0xf6f;
      assert s1.Peek(27) == 0x146;
      assert s1.Peek(28) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s6, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xb65

    requires s0.stack[19] == 0xba8

    requires s0.stack[24] == 0xf6f

    requires s0.stack[30] == 0x146

    requires s0.stack[31] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xb65;
      assert s1.Peek(19) == 0xba8;
      assert s1.Peek(24) == 0xf6f;
      assert s1.Peek(30) == 0x146;
      assert s1.Peek(31) == 0x14b;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s224(s11, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xb65

    requires s0.stack[18] == 0xba8

    requires s0.stack[23] == 0xf6f

    requires s0.stack[29] == 0x146

    requires s0.stack[30] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xb65;
      assert s1.Peek(18) == 0xba8;
      assert s1.Peek(23) == 0xf6f;
      assert s1.Peek(29) == 0x146;
      assert s1.Peek(30) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s7, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xb65

    requires s0.stack[15] == 0xba8

    requires s0.stack[20] == 0xf6f

    requires s0.stack[26] == 0x146

    requires s0.stack[27] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xb65;
      assert s1.Peek(15) == 0xba8;
      assert s1.Peek(20) == 0xf6f;
      assert s1.Peek(26) == 0x146;
      assert s1.Peek(27) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s5, gas - 1)
      else
        ExecuteFromCFGNode_s226(s5, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xf6f

    requires s0.stack[25] == 0x146

    requires s0.stack[26] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xb65;
      assert s1.Peek(15) == 0xba8;
      assert s1.Peek(20) == 0xf6f;
      assert s1.Peek(26) == 0x146;
      assert s1.Peek(27) == 0x14b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 227
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xf6f

    requires s0.stack[25] == 0x146

    requires s0.stack[26] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xb65;
      assert s1.Peek(14) == 0xba8;
      assert s1.Peek(19) == 0xf6f;
      assert s1.Peek(25) == 0x146;
      assert s1.Peek(26) == 0x14b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s3, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xb65

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xf6f

    requires s0.stack[23] == 0x146

    requires s0.stack[24] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb65;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xf6f;
      assert s1.Peek(23) == 0x146;
      assert s1.Peek(24) == 0x14b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s6, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 172
    * Starting at 0xb65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0xba8

    requires s0.stack[14] == 0xf6f

    requires s0.stack[20] == 0x146

    requires s0.stack[21] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xf6f;
      assert s1.Peek(20) == 0x146;
      assert s1.Peek(21) == 0x14b;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0xba8;
      assert s11.Peek(14) == 0xf6f;
      assert s11.Peek(20) == 0x146;
      assert s11.Peek(21) == 0x14b;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0b52);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s16, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 173
    * Starting at 0xb79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xf6f

    requires s0.stack[18] == 0x146

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xf6f;
      assert s1.Peek(18) == 0x146;
      assert s1.Peek(19) == 0x14b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s10, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 178
    * Starting at 0xba8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xf6f

    requires s0.stack[11] == 0x146

    requires s0.stack[12] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf6f;
      assert s1.Peek(11) == 0x146;
      assert s1.Peek(12) == 0x14b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s9, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 275
    * Starting at 0xf6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x146

    requires s0.stack[7] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x146;
      assert s1.Peek(7) == 0x14b;
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
      ExecuteFromCFGNode_s233(s10, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 31
    * Starting at 0x146
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14b;
      var s2 := Push2(s1, 0x031c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s3, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 65
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14b;
      var s2 := Push2(s1, 0x0324);
      var s3 := Push2(s2, 0x05a1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s4, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 85
    * Starting at 0x5a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x324

    requires s0.stack[3] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x324;
      assert s1.Peek(3) == 0x14b;
      var s2 := Push2(s1, 0x05a9);
      var s3 := Push2(s2, 0x09de);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s4, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5a9

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a9;
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s7, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 86
    * Starting at 0x5a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x14b;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x05c7);
      var s5 := Push2(s4, 0x01c3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s6, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 46
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x5c7

    requires s0.stack[2] == 0x324

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c7;
      assert s1.Peek(2) == 0x324;
      assert s1.Peek(5) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x5c7;
      assert s11.Peek(4) == 0x324;
      assert s11.Peek(7) == 0x14b;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s17, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 87
    * Starting at 0x5c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x324

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x324;
      assert s1.Peek(5) == 0x14b;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0626);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s6, gas - 1)
      else
        ExecuteFromCFGNode_s240(s6, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 88
    * Starting at 0x5e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x324

    requires s0.stack[3] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05ea);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x14b;
      var s2 := Push2(s1, 0x09de);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s3, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5ea

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s7, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 89
    * Starting at 0x5ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x14b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x061d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x61d;
      assert s11.Peek(3) == 0x324;
      assert s11.Peek(6) == 0x14b;
      var s12 := Push2(s11, 0x0d31);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s13, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x61d

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x61d;
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0x61d;
      assert s11.Peek(6) == 0x324;
      assert s11.Peek(9) == 0x14b;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s14, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0x61d

    requires s0.stack[7] == 0x324

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0x61d;
      assert s1.Peek(7) == 0x324;
      assert s1.Peek(10) == 0x14b;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s5, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0x61d

    requires s0.stack[9] == 0x324

    requires s0.stack[12] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0x61d;
      assert s1.Peek(9) == 0x324;
      assert s1.Peek(12) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s6, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0x61d

    requires s0.stack[12] == 0x324

    requires s0.stack[15] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0x61d;
      assert s1.Peek(12) == 0x324;
      assert s1.Peek(15) == 0x14b;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s247(s11, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0x61d

    requires s0.stack[11] == 0x324

    requires s0.stack[14] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0x61d;
      assert s1.Peek(11) == 0x324;
      assert s1.Peek(14) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s7, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0x61d

    requires s0.stack[8] == 0x324

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0x61d;
      assert s1.Peek(8) == 0x324;
      assert s1.Peek(11) == 0x14b;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s6, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x61d

    requires s0.stack[4] == 0x324

    requires s0.stack[7] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61d;
      assert s1.Peek(4) == 0x324;
      assert s1.Peek(7) == 0x14b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s6, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 90
    * Starting at 0x61d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x14b;
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

  /** Node 251
    * Segment Id for this node is: 91
    * Starting at 0x626
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x626 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x324

    requires s0.stack[3] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x324;
      assert s1.Peek(3) == 0x14b;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s2, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 66
    * Starting at 0x324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14b;
      var s2 := Push2(s1, 0x032e);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0848);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s6, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 114
    * Starting at 0x848
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x848 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x32e

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32e;
      assert s1.Peek(5) == 0x14b;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Dup3(s3);
      var s5 := MLoad(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x088c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s8, gas - 1)
      else
        ExecuteFromCFGNode_s254(s8, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 115
    * Starting at 0x852
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x852 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x32e

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x32e;
      assert s1.Peek(6) == 0x14b;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0883);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x11a3);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s11, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 317
    * Starting at 0x11a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x883

    requires s0.stack[4] == 0x32e

    requires s0.stack[7] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x883;
      assert s1.Peek(4) == 0x32e;
      assert s1.Peek(7) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x883;
      assert s11.Peek(7) == 0x32e;
      assert s11.Peek(10) == 0x14b;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11bc);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1180);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s18, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 314
    * Starting at 0x1180
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1180 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x11bc

    requires s0.stack[4] == 0x883

    requires s0.stack[7] == 0x32e

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11bc;
      assert s1.Peek(4) == 0x883;
      assert s1.Peek(7) == 0x32e;
      assert s1.Peek(10) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x118d);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x10da);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s7, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 306
    * Starting at 0x10da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x118d

    requires s0.stack[5] == 0x11bc

    requires s0.stack[8] == 0x883

    requires s0.stack[11] == 0x32e

    requires s0.stack[14] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x118d;
      assert s1.Peek(5) == 0x11bc;
      assert s1.Peek(8) == 0x883;
      assert s1.Peek(11) == 0x32e;
      assert s1.Peek(14) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x118d;
      assert s11.Peek(6) == 0x11bc;
      assert s11.Peek(9) == 0x883;
      assert s11.Peek(12) == 0x32e;
      assert s11.Peek(15) == 0x14b;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s15, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 315
    * Starting at 0x118d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x11bc

    requires s0.stack[6] == 0x883

    requires s0.stack[9] == 0x32e

    requires s0.stack[12] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(6) == 0x883;
      assert s1.Peek(9) == 0x32e;
      assert s1.Peek(12) == 0x14b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1198);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1157);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s7, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 313
    * Starting at 0x1157
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1198

    requires s0.stack[4] == 0x11bc

    requires s0.stack[7] == 0x883

    requires s0.stack[10] == 0x32e

    requires s0.stack[13] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1198;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(7) == 0x883;
      assert s1.Peek(10) == 0x32e;
      assert s1.Peek(13) == 0x14b;
      var s2 := Push32(s1, 0x617272617920706172616d65746572732073686f756c6420626520657175616c);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s8, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 316
    * Starting at 0x1198
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x11bc

    requires s0.stack[5] == 0x883

    requires s0.stack[8] == 0x32e

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(5) == 0x883;
      assert s1.Peek(8) == 0x32e;
      assert s1.Peek(11) == 0x14b;
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
      ExecuteFromCFGNode_s261(s10, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 318
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x883

    requires s0.stack[6] == 0x32e

    requires s0.stack[9] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x883;
      assert s1.Peek(6) == 0x32e;
      assert s1.Peek(9) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s7, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 116
    * Starting at 0x883
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x883 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x32e

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32e;
      assert s1.Peek(6) == 0x14b;
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

  /** Node 263
    * Segment Id for this node is: 117
    * Starting at 0x88c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x32e

    requires s0.stack[5] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32e;
      assert s1.Peek(5) == 0x14b;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s264(s2, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 118
    * Starting at 0x88f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x32e

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32e;
      assert s1.Peek(6) == 0x14b;
      var s2 := Dup3(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x09d9);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s8, gas - 1)
      else
        ExecuteFromCFGNode_s265(s8, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 119
    * Starting at 0x899
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x899 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x32e

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x32e;
      assert s1.Peek(7) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x08ab);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s8, gas - 1)
      else
        ExecuteFromCFGNode_s266(s8, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 120
    * Starting at 0x8a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x32e

    requires s0.stack[8] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08aa);
      assert s1.Peek(0) == 0x8aa;
      assert s1.Peek(6) == 0x32e;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s3, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x8aa

    requires s0.stack[6] == 0x32e

    requires s0.stack[9] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8aa;
      assert s1.Peek(6) == 0x32e;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 268
    * Segment Id for this node is: 122
    * Starting at 0x8ab
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x32e

    requires s0.stack[8] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x32e;
      assert s1.Peek(8) == 0x14b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup6(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(8) == 0x32e;
      assert s11.Peek(11) == 0x14b;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x08ca);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s17, gas - 1)
      else
        ExecuteFromCFGNode_s269(s17, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 123
    * Starting at 0x8c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x32e

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08c9);
      assert s1.Peek(0) == 0x8c9;
      assert s1.Peek(9) == 0x32e;
      assert s1.Peek(12) == 0x14b;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s3, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x8c9

    requires s0.stack[9] == 0x32e

    requires s0.stack[12] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8c9;
      assert s1.Peek(9) == 0x32e;
      assert s1.Peek(12) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 271
    * Segment Id for this node is: 125
    * Starting at 0x8ca
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x32e

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x32e;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x32e;
      assert s11.Peek(10) == 0x14b;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x32e;
      assert s21.Peek(9) == 0x14b;
      var s22 := Keccak256(s21);
      var s23 := Push1(s22, 0x00);
      var s24 := Push2(s23, 0x0100);
      var s25 := Exp(s24);
      var s26 := Dup2(s25);
      var s27 := SLoad(s26);
      var s28 := Dup2(s27);
      var s29 := Push20(s28, 0xffffffffffffffffffffffffffffffffffffffff);
      var s30 := Mul(s29);
      var s31 := Not(s30);
      assert s31.Peek(8) == 0x32e;
      assert s31.Peek(11) == 0x14b;
      var s32 := And(s31);
      var s33 := Swap1(s32);
      var s34 := Dup4(s33);
      var s35 := Push20(s34, 0xffffffffffffffffffffffffffffffffffffffff);
      var s36 := And(s35);
      var s37 := Mul(s36);
      var s38 := Or(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s272(s41, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 126
    * Starting at 0x94b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x32e

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(4) == 0x32e;
      assert s1.Peek(7) == 0x14b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x095d);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s275(s8, gas - 1)
      else
        ExecuteFromCFGNode_s273(s8, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 127
    * Starting at 0x955
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x955 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x32e

    requires s0.stack[8] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x095c);
      assert s1.Peek(0) == 0x95c;
      assert s1.Peek(6) == 0x32e;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s3, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x95c

    requires s0.stack[6] == 0x32e

    requires s0.stack[9] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x95c;
      assert s1.Peek(6) == 0x32e;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 275
    * Segment Id for this node is: 129
    * Starting at 0x95d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x32e

    requires s0.stack[8] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x32e;
      assert s1.Peek(8) == 0x14b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push32(s9, 0x22c5b7b2d8561d39f7f210b6b326a1aa69f15311163082308ac4877db6339dc1);
      var s11 := Dup4(s10);
      assert s11.Peek(6) == 0x32e;
      assert s11.Peek(9) == 0x14b;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MLoad(s13);
      var s15 := Dup2(s14);
      var s16 := Lt(s15);
      var s17 := Push2(s16, 0x09af);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s18, gas - 1)
      else
        ExecuteFromCFGNode_s276(s18, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 130
    * Starting at 0x9a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x32e

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09ae);
      assert s1.Peek(0) == 0x9ae;
      assert s1.Peek(8) == 0x32e;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s3, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x9ae

    requires s0.stack[8] == 0x32e

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9ae;
      assert s1.Peek(8) == 0x32e;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 278
    * Segment Id for this node is: 132
    * Starting at 0x9af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x32e

    requires s0.stack[10] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x32e;
      assert s1.Peek(10) == 0x14b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Push2(s9, 0x09c4);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x9c4;
      assert s11.Peek(8) == 0x32e;
      assert s11.Peek(11) == 0x14b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d31);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s14, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x9c4

    requires s0.stack[8] == 0x32e

    requires s0.stack[11] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9c4;
      assert s1.Peek(8) == 0x32e;
      assert s1.Peek(11) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0x9c4;
      assert s11.Peek(11) == 0x32e;
      assert s11.Peek(14) == 0x14b;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s14, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0x9c4

    requires s0.stack[12] == 0x32e

    requires s0.stack[15] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0x9c4;
      assert s1.Peek(12) == 0x32e;
      assert s1.Peek(15) == 0x14b;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s5, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0x9c4

    requires s0.stack[14] == 0x32e

    requires s0.stack[17] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0x9c4;
      assert s1.Peek(14) == 0x32e;
      assert s1.Peek(17) == 0x14b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s6, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0x9c4

    requires s0.stack[17] == 0x32e

    requires s0.stack[20] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0x9c4;
      assert s1.Peek(17) == 0x32e;
      assert s1.Peek(20) == 0x14b;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s283(s11, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0x9c4

    requires s0.stack[16] == 0x32e

    requires s0.stack[19] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0x9c4;
      assert s1.Peek(16) == 0x32e;
      assert s1.Peek(19) == 0x14b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s7, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0x9c4

    requires s0.stack[13] == 0x32e

    requires s0.stack[16] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0x9c4;
      assert s1.Peek(13) == 0x32e;
      assert s1.Peek(16) == 0x14b;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s6, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9c4

    requires s0.stack[9] == 0x32e

    requires s0.stack[12] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9c4;
      assert s1.Peek(9) == 0x32e;
      assert s1.Peek(12) == 0x14b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 133
    * Starting at 0x9c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x32e

    requires s0.stack[9] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x32e;
      assert s1.Peek(9) == 0x14b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log2(s7);
      var s9 := Dup1(s8);
      var s10 := Dup1(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x32e;
      assert s11.Peek(9) == 0x14b;
      var s12 := Add(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Push2(s15, 0x088f);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s17, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 134
    * Starting at 0x9d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x32e

    requires s0.stack[6] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32e;
      assert s1.Peek(6) == 0x14b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s5, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 67
    * Starting at 0x32e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x14b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s4, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 32
    * Starting at 0x14b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b as nat
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

  /** Node 290
    * Segment Id for this node is: 26
    * Starting at 0x101
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x011b);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0116);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x116;
      assert s11.Peek(3) == 0x11b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0dd4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s14, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 237
    * Starting at 0xdd4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x116

    requires s0.stack[3] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x116;
      assert s1.Peek(3) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0deb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s11, gas - 1)
      else
        ExecuteFromCFGNode_s292(s11, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 238
    * Starting at 0xde3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x116

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0dea);
      assert s1.Peek(0) == 0xdea;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x11b;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s3, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xdea

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xdea;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 294
    * Segment Id for this node is: 240
    * Starting at 0xdeb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x116

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x116;
      assert s1.Peek(5) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0e09);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s297(s11, gas - 1)
      else
        ExecuteFromCFGNode_s295(s11, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 241
    * Starting at 0xe01
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe01 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e08);
      assert s1.Peek(0) == 0xe08;
      assert s1.Peek(6) == 0x116;
      assert s1.Peek(7) == 0x11b;
      var s2 := Push2(s1, 0x09f5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s3, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 138
    * Starting at 0x9f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xe08

    requires s0.stack[6] == 0x116

    requires s0.stack[7] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe08;
      assert s1.Peek(6) == 0x116;
      assert s1.Peek(7) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 297
    * Segment Id for this node is: 243
    * Starting at 0xe09
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe09 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x11b;
      var s2 := Push2(s1, 0x0e15);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0d7e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s8, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 227
    * Starting at 0xd7e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe15

    requires s0.stack[8] == 0x116

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe15;
      assert s1.Peek(8) == 0x116;
      assert s1.Peek(9) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x0d94);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s10, gas - 1)
      else
        ExecuteFromCFGNode_s299(s10, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 228
    * Starting at 0xd8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xe15

    requires s0.stack[10] == 0x116

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d93);
      assert s1.Peek(0) == 0xd93;
      assert s1.Peek(5) == 0xe15;
      assert s1.Peek(11) == 0x116;
      assert s1.Peek(12) == 0x11b;
      var s2 := Push2(s1, 0x09fa);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s3, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 139
    * Starting at 0x9fa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xd93

    requires s0.stack[5] == 0xe15

    requires s0.stack[11] == 0x116

    requires s0.stack[12] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd93;
      assert s1.Peek(5) == 0xe15;
      assert s1.Peek(11) == 0x116;
      assert s1.Peek(12) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 301
    * Segment Id for this node is: 230
    * Starting at 0xd94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xe15

    requires s0.stack[10] == 0x116

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe15;
      assert s1.Peek(10) == 0x116;
      assert s1.Peek(11) == 0x11b;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0db1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s304(s11, gas - 1)
      else
        ExecuteFromCFGNode_s302(s11, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 231
    * Starting at 0xda9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xe15

    requires s0.stack[10] == 0x116

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0db0);
      assert s1.Peek(0) == 0xdb0;
      assert s1.Peek(5) == 0xe15;
      assert s1.Peek(11) == 0x116;
      assert s1.Peek(12) == 0x11b;
      var s2 := Push2(s1, 0x0d79);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s3, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 226
    * Starting at 0xd79
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xdb0

    requires s0.stack[5] == 0xe15

    requires s0.stack[11] == 0x116

    requires s0.stack[12] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xdb0;
      assert s1.Peek(5) == 0xe15;
      assert s1.Peek(11) == 0x116;
      assert s1.Peek(12) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 304
    * Segment Id for this node is: 233
    * Starting at 0xdb1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xe15

    requires s0.stack[10] == 0x116

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe15;
      assert s1.Peek(10) == 0x116;
      assert s1.Peek(11) == 0x11b;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Mul(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0xe15;
      assert s11.Peek(13) == 0x116;
      assert s11.Peek(14) == 0x11b;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0dcd);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s16, gas - 1)
      else
        ExecuteFromCFGNode_s305(s16, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 234
    * Starting at 0xdc5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xe15

    requires s0.stack[10] == 0x116

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0dcc);
      assert s1.Peek(0) == 0xdcc;
      assert s1.Peek(5) == 0xe15;
      assert s1.Peek(11) == 0x116;
      assert s1.Peek(12) == 0x11b;
      var s2 := Push2(s1, 0x0ab7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s3, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 154
    * Starting at 0xab7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xdcc

    requires s0.stack[5] == 0xe15

    requires s0.stack[11] == 0x116

    requires s0.stack[12] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xdcc;
      assert s1.Peek(5) == 0xe15;
      assert s1.Peek(11) == 0x116;
      assert s1.Peek(12) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 307
    * Segment Id for this node is: 236
    * Starting at 0xdcd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xe15

    requires s0.stack[10] == 0x116

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe15;
      assert s1.Peek(10) == 0x116;
      assert s1.Peek(11) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s7, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 244
    * Starting at 0xe15
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x116

    requires s0.stack[8] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x116;
      assert s1.Peek(8) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x116;
      assert s11.Peek(3) == 0x11b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s12, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 27
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11b;
      var s2 := Push2(s1, 0x0255);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s3, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 48
    * Starting at 0x255
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x255 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11b;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(6) == 0x11b;
      var s12 := Push2(s11, 0x0276);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s313(s13, gas - 1)
      else
        ExecuteFromCFGNode_s311(s13, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 49
    * Starting at 0x26e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0275);
      assert s1.Peek(0) == 0x275;
      assert s1.Peek(6) == 0x11b;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s3, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x275

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x275;
      assert s1.Peek(6) == 0x11b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 313
    * Segment Id for this node is: 51
    * Starting at 0x276
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x276 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Mul(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(8) == 0x11b;
      var s12 := Add(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x02a4);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s315(s20, gas - 1)
      else
        ExecuteFromCFGNode_s314(s20, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 52
    * Starting at 0x290
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x290 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(7) == 0x11b;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Mul(s5);
      var s7 := Dup1(s6);
      var s8 := CallDataSize(s7);
      var s9 := Dup4(s8);
      var s10 := CallDataCopy(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(9) == 0x11b;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s315(s18, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 53
    * Starting at 0x2a4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s316(s5, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 54
    * Starting at 0x2aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11b;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0311);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s402(s10, gas - 1)
      else
        ExecuteFromCFGNode_s317(s10, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 55
    * Starting at 0x2b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02e5);
      assert s1.Peek(0) == 0x2e5;
      assert s1.Peek(6) == 0x11b;
      var s2 := Dup6(s1);
      var s3 := Dup6(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x02cb);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s9, gas - 1)
      else
        ExecuteFromCFGNode_s318(s9, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 56
    * Starting at 0x2c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02ca);
      assert s1.Peek(0) == 0x2ca;
      assert s1.Peek(4) == 0x2e5;
      assert s1.Peek(10) == 0x11b;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s3, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x2ca

    requires s0.stack[4] == 0x2e5

    requires s0.stack[10] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2ca;
      assert s1.Peek(4) == 0x2e5;
      assert s1.Peek(10) == 0x11b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 320
    * Segment Id for this node is: 58
    * Starting at 0x2cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2e5;
      assert s1.Peek(9) == 0x11b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Mul(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x02e0);
      assert s11.Peek(0) == 0x2e0;
      assert s11.Peek(3) == 0x2e5;
      assert s11.Peek(9) == 0x11b;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0d4c);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s15, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 221
    * Starting at 0xd4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x2e0

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2e0;
      assert s1.Peek(3) == 0x2e5;
      assert s1.Peek(9) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d62);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s324(s10, gas - 1)
      else
        ExecuteFromCFGNode_s322(s10, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 222
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2e0

    requires s0.stack[4] == 0x2e5

    requires s0.stack[10] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d61);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0x2e0;
      assert s1.Peek(5) == 0x2e5;
      assert s1.Peek(11) == 0x11b;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s3, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xd61

    requires s0.stack[4] == 0x2e0

    requires s0.stack[5] == 0x2e5

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0x2e0;
      assert s1.Peek(5) == 0x2e5;
      assert s1.Peek(11) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 324
    * Segment Id for this node is: 224
    * Starting at 0xd62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2e0

    requires s0.stack[4] == 0x2e5

    requires s0.stack[10] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2e0;
      assert s1.Peek(4) == 0x2e5;
      assert s1.Peek(10) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d70);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b05);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s9, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xd70

    requires s0.stack[7] == 0x2e0

    requires s0.stack[8] == 0x2e5

    requires s0.stack[14] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd70;
      assert s1.Peek(7) == 0x2e0;
      assert s1.Peek(8) == 0x2e5;
      assert s1.Peek(14) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s10, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x2e0

    requires s0.stack[11] == 0x2e5

    requires s0.stack[17] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0x2e0;
      assert s1.Peek(11) == 0x2e5;
      assert s1.Peek(17) == 0x11b;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s5, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xd70

    requires s0.stack[12] == 0x2e0

    requires s0.stack[13] == 0x2e5

    requires s0.stack[19] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xd70;
      assert s1.Peek(12) == 0x2e0;
      assert s1.Peek(13) == 0x2e5;
      assert s1.Peek(19) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s6, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xd70

    requires s0.stack[15] == 0x2e0

    requires s0.stack[16] == 0x2e5

    requires s0.stack[22] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xd70;
      assert s1.Peek(15) == 0x2e0;
      assert s1.Peek(16) == 0x2e5;
      assert s1.Peek(22) == 0x11b;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s329(s11, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xd70

    requires s0.stack[14] == 0x2e0

    requires s0.stack[15] == 0x2e5

    requires s0.stack[21] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xd70;
      assert s1.Peek(14) == 0x2e0;
      assert s1.Peek(15) == 0x2e5;
      assert s1.Peek(21) == 0x11b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s7, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xd70

    requires s0.stack[11] == 0x2e0

    requires s0.stack[12] == 0x2e5

    requires s0.stack[18] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0x2e0;
      assert s1.Peek(12) == 0x2e5;
      assert s1.Peek(18) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s5, gas - 1)
      else
        ExecuteFromCFGNode_s331(s5, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x2e0

    requires s0.stack[11] == 0x2e5

    requires s0.stack[17] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0x2e0;
      assert s1.Peek(12) == 0x2e5;
      assert s1.Peek(18) == 0x11b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 332
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0x2e0

    requires s0.stack[11] == 0x2e5

    requires s0.stack[17] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0x2e0;
      assert s1.Peek(11) == 0x2e5;
      assert s1.Peek(17) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s3, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xd70

    requires s0.stack[8] == 0x2e0

    requires s0.stack[9] == 0x2e5

    requires s0.stack[15] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd70;
      assert s1.Peek(8) == 0x2e0;
      assert s1.Peek(9) == 0x2e5;
      assert s1.Peek(15) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s6, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 225
    * Starting at 0xd70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x2e0

    requires s0.stack[6] == 0x2e5

    requires s0.stack[12] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2e0;
      assert s1.Peek(6) == 0x2e5;
      assert s1.Peek(12) == 0x11b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s9, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 59
    * Starting at 0x2e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x2e5

    requires s0.stack[7] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e5;
      assert s1.Peek(7) == 0x11b;
      var s2 := Push2(s1, 0x0332);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s3, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 68
    * Starting at 0x332
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x332 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x2e5

    requires s0.stack[7] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e5;
      assert s1.Peek(7) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup5(s5);
      var s7 := Push20(s6, 0xffffffffffffffffffffffffffffffffffffffff);
      var s8 := And(s7);
      var s9 := Push20(s8, 0xffffffffffffffffffffffffffffffffffffffff);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x2e5;
      assert s11.Peek(13) == 0x11b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x00);
      var s21 := Keccak256(s20);
      assert s21.Peek(4) == 0x2e5;
      assert s21.Peek(10) == 0x11b;
      var s22 := Push1(s21, 0x00);
      var s23 := Swap1(s22);
      var s24 := SLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push2(s25, 0x0100);
      var s27 := Exp(s26);
      var s28 := Swap1(s27);
      var s29 := Div(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(4) == 0x2e5;
      assert s31.Peek(10) == 0x11b;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      var s35 := Push20(s34, 0xffffffffffffffffffffffffffffffffffffffff);
      var s36 := And(s35);
      var s37 := Dup2(s36);
      var s38 := Push20(s37, 0xffffffffffffffffffffffffffffffffffffffff);
      var s39 := And(s38);
      var s40 := Eq(s39);
      var s41 := Push2(s40, 0x044c);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s337(s41, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 69
    * Starting at 0x3cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x44c

    requires s0.stack[5] == 0x2e5

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpI(s0);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s0.stack[1] > 0 then
        ExecuteFromCFGNode_s391(s1, gas - 1)
      else
        ExecuteFromCFGNode_s338(s1, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 70
    * Starting at 0x3cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2e5;
      assert s1.Peek(10) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Push4(s4, 0xfeaf968c);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Push4(s8, 0xffffffff);
      var s10 := And(s9);
      var s11 := Push1(s10, 0xe0);
      assert s11.Peek(9) == 0x2e5;
      assert s11.Peek(15) == 0x11b;
      var s12 := Shl(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0xa0);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(11) == 0x2e5;
      assert s21.Peek(17) == 0x11b;
      var s22 := Sub(s21);
      var s23 := Dup2(s22);
      var s24 := Dup7(s23);
      var s25 := Gas(s24);
      var s26 := StaticCall(s25);
      var s27 := IsZero(s26);
      var s28 := Dup1(s27);
      var s29 := IsZero(s28);
      var s30 := Push2(s29, 0x0418);
      var s31 := JumpI(s30);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s30.stack[1] > 0 then
        ExecuteFromCFGNode_s340(s31, gas - 1)
      else
        ExecuteFromCFGNode_s339(s31, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 71
    * Starting at 0x40f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x2e5

    requires s0.stack[14] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x2e5;
      assert s1.Peek(15) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 340
    * Segment Id for this node is: 72
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x2e5

    requires s0.stack[14] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x2e5;
      assert s1.Peek(14) == 0x11b;
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
      assert s11.Peek(8) == 0x2e5;
      assert s11.Peek(14) == 0x11b;
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
      assert s21.Peek(7) == 0x2e5;
      assert s21.Peek(13) == 0x11b;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x043c);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x105f);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s28, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 297
    * Starting at 0x105f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x43c

    requires s0.stack[7] == 0x2e5

    requires s0.stack[13] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x43c;
      assert s1.Peek(7) == 0x2e5;
      assert s1.Peek(13) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Push1(s6, 0xa0);
      var s8 := Dup7(s7);
      var s9 := Dup9(s8);
      var s10 := Sub(s9);
      var s11 := SLt(s10);
      assert s11.Peek(8) == 0x43c;
      assert s11.Peek(13) == 0x2e5;
      assert s11.Peek(19) == 0x11b;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x107b);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s344(s14, gas - 1)
      else
        ExecuteFromCFGNode_s342(s14, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 298
    * Starting at 0x1073
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1073 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x43c

    requires s0.stack[12] == 0x2e5

    requires s0.stack[18] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x107a);
      assert s1.Peek(0) == 0x107a;
      assert s1.Peek(8) == 0x43c;
      assert s1.Peek(13) == 0x2e5;
      assert s1.Peek(19) == 0x11b;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s3, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x107a

    requires s0.stack[8] == 0x43c

    requires s0.stack[13] == 0x2e5

    requires s0.stack[19] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x107a;
      assert s1.Peek(8) == 0x43c;
      assert s1.Peek(13) == 0x2e5;
      assert s1.Peek(19) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 344
    * Segment Id for this node is: 300
    * Starting at 0x107b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x43c

    requires s0.stack[12] == 0x2e5

    requires s0.stack[18] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x43c;
      assert s1.Peek(12) == 0x2e5;
      assert s1.Peek(18) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1089);
      var s4 := Dup9(s3);
      var s5 := Dup3(s4);
      var s6 := Dup10(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0fff);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s9, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 286
    * Starting at 0xfff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x1089

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x2e5

    requires s0.stack[22] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1089;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x2e5;
      assert s1.Peek(22) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x100e);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fe8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s10, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 282
    * Starting at 0xfe8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x1089

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x1089;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Push2(s1, 0x0ff1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fd2);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s5, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 281
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xff1

    requires s0.stack[3] == 0x100e

    requires s0.stack[7] == 0x1089

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x2e5

    requires s0.stack[27] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xff1;
      assert s1.Peek(3) == 0x100e;
      assert s1.Peek(7) == 0x1089;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x2e5;
      assert s1.Peek(27) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := PushN(s2, 10, 0xffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s348(s11, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 283
    * Starting at 0xff1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0x100e

    requires s0.stack[6] == 0x1089

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x2e5

    requires s0.stack[26] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x1089;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ffc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s350(s5, gas - 1)
      else
        ExecuteFromCFGNode_s349(s5, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 284
    * Starting at 0xff8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x1089

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x1089;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 350
    * Segment Id for this node is: 285
    * Starting at 0xffc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x1089

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x1089;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s3, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 287
    * Starting at 0x100e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x1089

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x2e5

    requires s0.stack[23] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1089;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x2e5;
      assert s1.Peek(23) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s6, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 301
    * Starting at 0x1089
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1089 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x2e5

    requires s0.stack[20] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x2e5;
      assert s1.Peek(20) == 0x11b;
      var s2 := Swap6(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x109a);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x1035);
      assert s11.Peek(0) == 0x1035;
      assert s11.Peek(3) == 0x109a;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x2e5;
      assert s11.Peek(23) == 0x11b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s12, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 293
    * Starting at 0x1035
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1035 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x109a

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x2e5

    requires s0.stack[22] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109a;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x2e5;
      assert s1.Peek(22) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x101e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s10, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 289
    * Starting at 0x101e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1044

    requires s0.stack[5] == 0x109a

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1044;
      assert s1.Peek(5) == 0x109a;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Push2(s1, 0x1027);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x1014);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s5, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 288
    * Starting at 0x1014
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1014 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0x1027

    requires s0.stack[3] == 0x1044

    requires s0.stack[7] == 0x109a

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x2e5

    requires s0.stack[27] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1027;
      assert s1.Peek(3) == 0x1044;
      assert s1.Peek(7) == 0x109a;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x2e5;
      assert s1.Peek(27) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s9, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 290
    * Starting at 0x1027
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1027 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0x1044

    requires s0.stack[6] == 0x109a

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x2e5

    requires s0.stack[26] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1044;
      assert s1.Peek(6) == 0x109a;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x1032);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s358(s5, gas - 1)
      else
        ExecuteFromCFGNode_s357(s5, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 291
    * Starting at 0x102e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1044

    requires s0.stack[5] == 0x109a

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1044;
      assert s1.Peek(6) == 0x109a;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 358
    * Segment Id for this node is: 292
    * Starting at 0x1032
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1032 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1044

    requires s0.stack[5] == 0x109a

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1044;
      assert s1.Peek(5) == 0x109a;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s3, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 294
    * Starting at 0x1044
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x109a

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x2e5

    requires s0.stack[23] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x109a;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x2e5;
      assert s1.Peek(23) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s6, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 302
    * Starting at 0x109a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x2e5

    requires s0.stack[20] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x2e5;
      assert s1.Peek(20) == 0x11b;
      var s2 := Swap5(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x10ab);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x104a);
      assert s11.Peek(0) == 0x104a;
      assert s11.Peek(3) == 0x10ab;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x2e5;
      assert s11.Peek(23) == 0x11b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s12, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 295
    * Starting at 0x104a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x10ab

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x2e5

    requires s0.stack[22] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ab;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x2e5;
      assert s1.Peek(22) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x1059);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0be7);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s10, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 184
    * Starting at 0xbe7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10ab

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10ab;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Push2(s1, 0x0bf0);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s5, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xbf0

    requires s0.stack[3] == 0x1059

    requires s0.stack[7] == 0x10ab

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x2e5

    requires s0.stack[27] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbf0;
      assert s1.Peek(3) == 0x1059;
      assert s1.Peek(7) == 0x10ab;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x2e5;
      assert s1.Peek(27) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s9, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 185
    * Starting at 0xbf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0x1059

    requires s0.stack[6] == 0x10ab

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x2e5

    requires s0.stack[26] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10ab;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s366(s5, gas - 1)
      else
        ExecuteFromCFGNode_s365(s5, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 186
    * Starting at 0xbf7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10ab

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10ab;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 366
    * Segment Id for this node is: 187
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10ab

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10ab;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s3, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 296
    * Starting at 0x1059
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1059 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x10ab

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x2e5

    requires s0.stack[23] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10ab;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x2e5;
      assert s1.Peek(23) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s6, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 303
    * Starting at 0x10ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x2e5

    requires s0.stack[20] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x2e5;
      assert s1.Peek(20) == 0x11b;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Push2(s5, 0x10bc);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x104a);
      assert s11.Peek(0) == 0x104a;
      assert s11.Peek(3) == 0x10bc;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x2e5;
      assert s11.Peek(23) == 0x11b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s12, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 295
    * Starting at 0x104a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x10bc

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x2e5

    requires s0.stack[22] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10bc;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x2e5;
      assert s1.Peek(22) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x1059);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0be7);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s10, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 184
    * Starting at 0xbe7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10bc

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10bc;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Push2(s1, 0x0bf0);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s5, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xbf0

    requires s0.stack[3] == 0x1059

    requires s0.stack[7] == 0x10bc

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x2e5

    requires s0.stack[27] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbf0;
      assert s1.Peek(3) == 0x1059;
      assert s1.Peek(7) == 0x10bc;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x2e5;
      assert s1.Peek(27) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s9, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 185
    * Starting at 0xbf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0x1059

    requires s0.stack[6] == 0x10bc

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x2e5

    requires s0.stack[26] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10bc;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s374(s5, gas - 1)
      else
        ExecuteFromCFGNode_s373(s5, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 186
    * Starting at 0xbf7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10bc

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1059;
      assert s1.Peek(6) == 0x10bc;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 374
    * Segment Id for this node is: 187
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x1059

    requires s0.stack[5] == 0x10bc

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1059;
      assert s1.Peek(5) == 0x10bc;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s3, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 296
    * Starting at 0x1059
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1059 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x10bc

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x2e5

    requires s0.stack[23] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10bc;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x2e5;
      assert s1.Peek(23) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s6, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 304
    * Starting at 0x10bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x2e5

    requires s0.stack[20] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x2e5;
      assert s1.Peek(20) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x80);
      var s6 := Push2(s5, 0x10cd);
      var s7 := Dup9(s6);
      var s8 := Dup3(s7);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0fff);
      assert s11.Peek(0) == 0xfff;
      assert s11.Peek(3) == 0x10cd;
      assert s11.Peek(12) == 0x43c;
      assert s11.Peek(17) == 0x2e5;
      assert s11.Peek(23) == 0x11b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s12, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 286
    * Starting at 0xfff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x10cd

    requires s0.stack[11] == 0x43c

    requires s0.stack[16] == 0x2e5

    requires s0.stack[22] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10cd;
      assert s1.Peek(11) == 0x43c;
      assert s1.Peek(16) == 0x2e5;
      assert s1.Peek(22) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x100e);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0fe8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s10, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 282
    * Starting at 0xfe8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x10cd

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x10cd;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Push2(s1, 0x0ff1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0fd2);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s5, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 281
    * Starting at 0xfd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[1] == 0xff1

    requires s0.stack[3] == 0x100e

    requires s0.stack[7] == 0x10cd

    requires s0.stack[16] == 0x43c

    requires s0.stack[21] == 0x2e5

    requires s0.stack[27] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xff1;
      assert s1.Peek(3) == 0x100e;
      assert s1.Peek(7) == 0x10cd;
      assert s1.Peek(16) == 0x43c;
      assert s1.Peek(21) == 0x2e5;
      assert s1.Peek(27) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := PushN(s2, 10, 0xffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s11, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 283
    * Starting at 0xff1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0x100e

    requires s0.stack[6] == 0x10cd

    requires s0.stack[15] == 0x43c

    requires s0.stack[20] == 0x2e5

    requires s0.stack[26] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x10cd;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0ffc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s382(s5, gas - 1)
      else
        ExecuteFromCFGNode_s381(s5, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 284
    * Starting at 0xff8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x10cd

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x100e;
      assert s1.Peek(6) == 0x10cd;
      assert s1.Peek(15) == 0x43c;
      assert s1.Peek(20) == 0x2e5;
      assert s1.Peek(26) == 0x11b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 382
    * Segment Id for this node is: 285
    * Starting at 0xffc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[1] == 0x100e

    requires s0.stack[5] == 0x10cd

    requires s0.stack[14] == 0x43c

    requires s0.stack[19] == 0x2e5

    requires s0.stack[25] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x100e;
      assert s1.Peek(5) == 0x10cd;
      assert s1.Peek(14) == 0x43c;
      assert s1.Peek(19) == 0x2e5;
      assert s1.Peek(25) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s3, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 287
    * Starting at 0x100e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0x10cd

    requires s0.stack[12] == 0x43c

    requires s0.stack[17] == 0x2e5

    requires s0.stack[23] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10cd;
      assert s1.Peek(12) == 0x43c;
      assert s1.Peek(17) == 0x2e5;
      assert s1.Peek(23) == 0x11b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s6, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 305
    * Starting at 0x10cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[9] == 0x43c

    requires s0.stack[14] == 0x2e5

    requires s0.stack[20] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x43c;
      assert s1.Peek(14) == 0x2e5;
      assert s1.Peek(20) == 0x11b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap6(s8);
      var s10 := Swap1(s9);
      var s11 := Swap4(s10);
      assert s11.Peek(1) == 0x43c;
      assert s11.Peek(11) == 0x2e5;
      assert s11.Peek(17) == 0x11b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s13, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 73
    * Starting at 0x43c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[9] == 0x2e5

    requires s0.stack[15] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x2e5;
      assert s1.Peek(15) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Dup1(s7);
      var s9 := Swap3(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0x2e5;
      assert s11.Peek(9) == 0x11b;
      var s12 := Pop(s11);
      var s13 := Push2(s12, 0x0516);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s14, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 78
    * Starting at 0x516
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x516 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2e5

    requires s0.stack[8] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2e5;
      assert s1.Peek(8) == 0x11b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s5, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 60
    * Starting at 0x2e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x11b;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x02f8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s390(s9, gas - 1)
      else
        ExecuteFromCFGNode_s388(s9, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 61
    * Starting at 0x2f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f7);
      assert s1.Peek(0) == 0x2f7;
      assert s1.Peek(9) == 0x11b;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s3, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x2f7

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f7;
      assert s1.Peek(9) == 0x11b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 390
    * Segment Id for this node is: 63
    * Starting at 0x2f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x11b;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x11b;
      var s12 := Dup1(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Add(s14);
      var s16 := Swap2(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Push2(s18, 0x02aa);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s20, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 74
    * Starting at 0x44c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2e5;
      assert s1.Peek(9) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x02);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x2e5;
      assert s11.Peek(12) == 0x11b;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x2e5;
      assert s21.Peek(11) == 0x11b;
      var s22 := Eq(s21);
      var s23 := Push2(s22, 0x04db);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s393(s24, gas - 1)
      else
        ExecuteFromCFGNode_s392(s24, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 75
    * Starting at 0x494
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x494 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(4) == 0x2e5;
      assert s1.Peek(10) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup5(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x2e5;
      assert s11.Peek(11) == 0x11b;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(3) == 0x2e5;
      assert s21.Peek(9) == 0x11b;
      var s22 := Pop(s21);
      var s23 := Push2(s22, 0x0516);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s24, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 76
    * Starting at 0x4db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2e5

    requires s0.stack[9] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2e5;
      assert s1.Peek(9) == 0x11b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x050d);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x1137);
      assert s11.Peek(0) == 0x1137;
      assert s11.Peek(2) == 0x50d;
      assert s11.Peek(6) == 0x2e5;
      assert s11.Peek(12) == 0x11b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s12, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 311
    * Starting at 0x1137
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x50d

    requires s0.stack[5] == 0x2e5

    requires s0.stack[11] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x50d;
      assert s1.Peek(5) == 0x2e5;
      assert s1.Peek(11) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x50d;
      assert s11.Peek(8) == 0x2e5;
      assert s11.Peek(14) == 0x11b;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1150);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1114);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s18, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 308
    * Starting at 0x1114
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x1150

    requires s0.stack[4] == 0x50d

    requires s0.stack[8] == 0x2e5

    requires s0.stack[14] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1150;
      assert s1.Peek(4) == 0x50d;
      assert s1.Peek(8) == 0x2e5;
      assert s1.Peek(14) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x1121);
      var s4 := Push1(s3, 0x0f);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x10da);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s7, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 306
    * Starting at 0x10da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1121

    requires s0.stack[5] == 0x1150

    requires s0.stack[8] == 0x50d

    requires s0.stack[12] == 0x2e5

    requires s0.stack[18] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1121;
      assert s1.Peek(5) == 0x1150;
      assert s1.Peek(8) == 0x50d;
      assert s1.Peek(12) == 0x2e5;
      assert s1.Peek(18) == 0x11b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1121;
      assert s11.Peek(6) == 0x1150;
      assert s11.Peek(9) == 0x50d;
      assert s11.Peek(13) == 0x2e5;
      assert s11.Peek(19) == 0x11b;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s15, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 309
    * Starting at 0x1121
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x1150

    requires s0.stack[6] == 0x50d

    requires s0.stack[10] == 0x2e5

    requires s0.stack[16] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1150;
      assert s1.Peek(6) == 0x50d;
      assert s1.Peek(10) == 0x2e5;
      assert s1.Peek(16) == 0x11b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x112c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x10eb);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s7, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 307
    * Starting at 0x10eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x112c

    requires s0.stack[4] == 0x1150

    requires s0.stack[7] == 0x50d

    requires s0.stack[11] == 0x2e5

    requires s0.stack[17] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x112c;
      assert s1.Peek(4) == 0x1150;
      assert s1.Peek(7) == 0x50d;
      assert s1.Peek(11) == 0x2e5;
      assert s1.Peek(17) == 0x11b;
      var s2 := Push32(s1, 0x6173736574206e6f7420666f756e640000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s8, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 310
    * Starting at 0x112c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x1150

    requires s0.stack[5] == 0x50d

    requires s0.stack[9] == 0x2e5

    requires s0.stack[15] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1150;
      assert s1.Peek(5) == 0x50d;
      assert s1.Peek(9) == 0x2e5;
      assert s1.Peek(15) == 0x11b;
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
      ExecuteFromCFGNode_s400(s10, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 312
    * Starting at 0x1150
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x50d

    requires s0.stack[7] == 0x2e5

    requires s0.stack[13] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x50d;
      assert s1.Peek(7) == 0x2e5;
      assert s1.Peek(13) == 0x11b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s7, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 77
    * Starting at 0x50d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x2e5

    requires s0.stack[10] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2e5;
      assert s1.Peek(10) == 0x11b;
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

  /** Node 402
    * Segment Id for this node is: 64
    * Starting at 0x311
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x311 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x11b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11b;
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s11, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 28
    * Starting at 0x11b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0128);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0edf);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s8, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 262
    * Starting at 0xedf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(5) == 0x128;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0ef9);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0e81);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s19, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 253
    * Starting at 0xe81
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xef9

    requires s0.stack[6] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xef9;
      assert s1.Peek(6) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e8c);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0e21);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s6, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 245
    * Starting at 0xe21
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xe8c

    requires s0.stack[5] == 0xef9

    requires s0.stack[9] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe8c;
      assert s1.Peek(5) == 0xef9;
      assert s1.Peek(9) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s10, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 254
    * Starting at 0xe8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xef9

    requires s0.stack[8] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xef9;
      assert s1.Peek(8) == 0x128;
      var s2 := Push2(s1, 0x0e96);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0e2c);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s6, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 246
    * Starting at 0xe2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xe96

    requires s0.stack[7] == 0xef9

    requires s0.stack[11] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe96;
      assert s1.Peek(7) == 0xef9;
      assert s1.Peek(11) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xe96;
      assert s11.Peek(8) == 0xef9;
      assert s11.Peek(12) == 0x128;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s409(s15, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 255
    * Starting at 0xe96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xef9

    requires s0.stack[9] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xef9;
      assert s1.Peek(9) == 0x128;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0ea1);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e3d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s7, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 247
    * Starting at 0xe3d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xea1

    requires s0.stack[6] == 0xef9

    requires s0.stack[10] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xea1;
      assert s1.Peek(6) == 0xef9;
      assert s1.Peek(10) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xea1;
      assert s11.Peek(7) == 0xef9;
      assert s11.Peek(11) == 0x128;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s14, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 256
    * Starting at 0xea1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xef9

    requires s0.stack[9] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xef9;
      assert s1.Peek(9) == 0x128;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s412(s3, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 257
    * Starting at 0xea5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0xef9

    requires s0.stack[11] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xef9;
      assert s1.Peek(11) == 0x128;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ed2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s422(s7, gas - 1)
      else
        ExecuteFromCFGNode_s413(s7, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 258
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0xef9

    requires s0.stack[11] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(8) == 0xef9;
      assert s1.Peek(12) == 0x128;
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x0eb9);
      var s4 := Dup9(s3);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0e5c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s7, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 250
    * Starting at 0xe5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xeb9

    requires s0.stack[11] == 0xef9

    requires s0.stack[15] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeb9;
      assert s1.Peek(11) == 0xef9;
      assert s1.Peek(15) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0e68);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e4d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s7, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 248
    * Starting at 0xe4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xe68

    requires s0.stack[6] == 0xeb9

    requires s0.stack[15] == 0xef9

    requires s0.stack[19] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe68;
      assert s1.Peek(6) == 0xeb9;
      assert s1.Peek(15) == 0xef9;
      assert s1.Peek(19) == 0x128;
      var s2 := Push2(s1, 0x0e56);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s5, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xe56

    requires s0.stack[4] == 0xe68

    requires s0.stack[8] == 0xeb9

    requires s0.stack[17] == 0xef9

    requires s0.stack[21] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe56;
      assert s1.Peek(4) == 0xe68;
      assert s1.Peek(8) == 0xeb9;
      assert s1.Peek(17) == 0xef9;
      assert s1.Peek(21) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s9, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 249
    * Starting at 0xe56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xe68

    requires s0.stack[7] == 0xeb9

    requires s0.stack[16] == 0xef9

    requires s0.stack[20] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe68;
      assert s1.Peek(7) == 0xeb9;
      assert s1.Peek(16) == 0xef9;
      assert s1.Peek(20) == 0x128;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s6, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 251
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xeb9

    requires s0.stack[12] == 0xef9

    requires s0.stack[16] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xeb9;
      assert s1.Peek(12) == 0xef9;
      assert s1.Peek(16) == 0x128;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s11, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 259
    * Starting at 0xeb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[9] == 0xef9

    requires s0.stack[13] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xef9;
      assert s1.Peek(13) == 0x128;
      var s2 := Swap(s1, 8);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0ec4);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0e74);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s7, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 252
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xec4

    requires s0.stack[10] == 0xef9

    requires s0.stack[14] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec4;
      assert s1.Peek(10) == 0xef9;
      assert s1.Peek(14) == 0x128;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s11, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 260
    * Starting at 0xec4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[9] == 0xef9

    requires s0.stack[13] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xef9;
      assert s1.Peek(13) == 0x128;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Push2(s9, 0x0ea5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s11, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 261
    * Starting at 0xed2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0xef9

    requires s0.stack[11] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xef9;
      assert s1.Peek(11) == 0x128;
      var s2 := Pop(s1);
      var s3 := Dup6(s2);
      var s4 := Swap4(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0xef9;
      assert s11.Peek(6) == 0x128;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s13, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 263
    * Starting at 0xef9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x128;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s8, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 29
    * Starting at 0x128
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128 as nat
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

  /** Node 425
    * Segment Id for this node is: 9
    * Starting at 0x5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x08561b2c);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x008d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s490(s6, gas - 1)
      else
        ExecuteFromCFGNode_s426(s6, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 10
    * Starting at 0x67
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00a9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s5, gas - 1)
      else
        ExecuteFromCFGNode_s427(s5, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00b3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s455(s5, gas - 1)
      else
        ExecuteFromCFGNode_s428(s5, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x92bf2be0);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00d1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 22
    * Starting at 0xd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00eb);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x00e6);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0xe6;
      assert s11.Peek(3) == 0xeb;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d4c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s14, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 221
    * Starting at 0xd4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4c as nat
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
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d62);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s433(s10, gas - 1)
      else
        ExecuteFromCFGNode_s431(s10, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 222
    * Starting at 0xd5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xe6

    requires s0.stack[4] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d61);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0xe6;
      assert s1.Peek(5) == 0xeb;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s3, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xd61

    requires s0.stack[4] == 0xe6

    requires s0.stack[5] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd61;
      assert s1.Peek(4) == 0xe6;
      assert s1.Peek(5) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 433
    * Segment Id for this node is: 224
    * Starting at 0xd62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xe6

    requires s0.stack[4] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe6;
      assert s1.Peek(4) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d70);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b05);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s9, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd70

    requires s0.stack[7] == 0xe6

    requires s0.stack[8] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd70;
      assert s1.Peek(7) == 0xe6;
      assert s1.Peek(8) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s10, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0xe6

    requires s0.stack[11] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0xe6;
      assert s1.Peek(11) == 0xeb;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s5, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xd70

    requires s0.stack[12] == 0xe6

    requires s0.stack[13] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xd70;
      assert s1.Peek(12) == 0xe6;
      assert s1.Peek(13) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s437(s6, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xd70

    requires s0.stack[15] == 0xe6

    requires s0.stack[16] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xd70;
      assert s1.Peek(15) == 0xe6;
      assert s1.Peek(16) == 0xeb;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s438(s11, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xd70

    requires s0.stack[14] == 0xe6

    requires s0.stack[15] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xd70;
      assert s1.Peek(14) == 0xe6;
      assert s1.Peek(15) == 0xeb;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s7, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xd70

    requires s0.stack[11] == 0xe6

    requires s0.stack[12] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0xe6;
      assert s1.Peek(12) == 0xeb;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s441(s5, gas - 1)
      else
        ExecuteFromCFGNode_s440(s5, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0xe6

    requires s0.stack[11] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xd70;
      assert s1.Peek(11) == 0xe6;
      assert s1.Peek(12) == 0xeb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 441
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xd70

    requires s0.stack[10] == 0xe6

    requires s0.stack[11] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xd70;
      assert s1.Peek(10) == 0xe6;
      assert s1.Peek(11) == 0xeb;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s3, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd70

    requires s0.stack[8] == 0xe6

    requires s0.stack[9] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd70;
      assert s1.Peek(8) == 0xe6;
      assert s1.Peek(9) == 0xeb;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s6, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 225
    * Starting at 0xd70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xe6

    requires s0.stack[6] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe6;
      assert s1.Peek(6) == 0xeb;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s9, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 23
    * Starting at 0xe6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb;
      var s2 := Push2(s1, 0x01ec);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s3, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 47
    * Starting at 0x1ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xeb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xeb;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0xeb;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Keccak256(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(4) == 0xeb;
      var s22 := Swap1(s21);
      var s23 := SLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x0100);
      var s26 := Exp(s25);
      var s27 := Swap1(s26);
      var s28 := Div(s27);
      var s29 := Push20(s28, 0xffffffffffffffffffffffffffffffffffffffff);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(3) == 0xeb;
      var s32 := Pop(s31);
      var s33 := Swap2(s32);
      var s34 := Swap1(s33);
      var s35 := Pop(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s36, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 24
    * Starting at 0xeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
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
      var s7 := Push2(s6, 0x0d31);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s8, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0xf8;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s14, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0xf8;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s449(s5, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0xf8;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s6, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0xf8;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s451(s11, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0xf8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s7, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0xf8;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s6, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xf8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s6, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 25
    * Starting at 0xf8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
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

  /** Node 455
    * Segment Id for this node is: 19
    * Starting at 0xb3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00bb);
      var s3 := Push2(s2, 0x01c3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s4, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 46
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xbb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbb;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0xbb;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s457(s17, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 20
    * Starting at 0xbb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00c8);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d31);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s8, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc8;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0xc8;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s14, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0xc8;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s5, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0xc8;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s6, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0xc8;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s462(s11, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0xc8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s7, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0xc8;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s6, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xc8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s6, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 21
    * Starting at 0xc8
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8 as nat
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

  /** Node 466
    * Segment Id for this node is: 17
    * Starting at 0xa9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b1);
      var s3 := Push2(s2, 0x01af);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s4, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 43
    * Starting at 0x1af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb1;
      var s2 := Push2(s1, 0x01b7);
      var s3 := Push2(s2, 0x05a1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s4, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 85
    * Starting at 0x5a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x1b7

    requires s0.stack[1] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b7;
      assert s1.Peek(1) == 0xb1;
      var s2 := Push2(s1, 0x05a9);
      var s3 := Push2(s2, 0x09de);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s4, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x5a9

    requires s0.stack[1] == 0x1b7

    requires s0.stack[2] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a9;
      assert s1.Peek(1) == 0x1b7;
      assert s1.Peek(2) == 0xb1;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s7, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 86
    * Starting at 0x5a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x1b7

    requires s0.stack[2] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b7;
      assert s1.Peek(2) == 0xb1;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x05c7);
      var s5 := Push2(s4, 0x01c3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s6, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 46
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x5c7

    requires s0.stack[2] == 0x1b7

    requires s0.stack[3] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c7;
      assert s1.Peek(2) == 0x1b7;
      assert s1.Peek(3) == 0xb1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x5c7;
      assert s11.Peek(4) == 0x1b7;
      assert s11.Peek(5) == 0xb1;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s17, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 87
    * Starting at 0x5c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1b7

    requires s0.stack[3] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b7;
      assert s1.Peek(3) == 0xb1;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0626);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s484(s6, gas - 1)
      else
        ExecuteFromCFGNode_s473(s6, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 88
    * Starting at 0x5e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x1b7

    requires s0.stack[1] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05ea);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x1b7;
      assert s1.Peek(2) == 0xb1;
      var s2 := Push2(s1, 0x09de);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s474(s3, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x5ea

    requires s0.stack[1] == 0x1b7

    requires s0.stack[2] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x1b7;
      assert s1.Peek(2) == 0xb1;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s7, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 89
    * Starting at 0x5ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x1b7

    requires s0.stack[2] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b7;
      assert s1.Peek(2) == 0xb1;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x061d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x61d;
      assert s11.Peek(3) == 0x1b7;
      assert s11.Peek(4) == 0xb1;
      var s12 := Push2(s11, 0x0d31);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s13, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x61d

    requires s0.stack[3] == 0x1b7

    requires s0.stack[4] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x61d;
      assert s1.Peek(3) == 0x1b7;
      assert s1.Peek(4) == 0xb1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0x61d;
      assert s11.Peek(6) == 0x1b7;
      assert s11.Peek(7) == 0xb1;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s14, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0x61d

    requires s0.stack[7] == 0x1b7

    requires s0.stack[8] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0x61d;
      assert s1.Peek(7) == 0x1b7;
      assert s1.Peek(8) == 0xb1;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s5, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0x61d

    requires s0.stack[9] == 0x1b7

    requires s0.stack[10] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0x61d;
      assert s1.Peek(9) == 0x1b7;
      assert s1.Peek(10) == 0xb1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s6, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0x61d

    requires s0.stack[12] == 0x1b7

    requires s0.stack[13] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0x61d;
      assert s1.Peek(12) == 0x1b7;
      assert s1.Peek(13) == 0xb1;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s480(s11, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0x61d

    requires s0.stack[11] == 0x1b7

    requires s0.stack[12] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0x61d;
      assert s1.Peek(11) == 0x1b7;
      assert s1.Peek(12) == 0xb1;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s7, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0x61d

    requires s0.stack[8] == 0x1b7

    requires s0.stack[9] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0x61d;
      assert s1.Peek(8) == 0x1b7;
      assert s1.Peek(9) == 0xb1;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s6, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x61d

    requires s0.stack[4] == 0x1b7

    requires s0.stack[5] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61d;
      assert s1.Peek(4) == 0x1b7;
      assert s1.Peek(5) == 0xb1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s6, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 90
    * Starting at 0x61d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x1b7

    requires s0.stack[2] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b7;
      assert s1.Peek(2) == 0xb1;
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

  /** Node 484
    * Segment Id for this node is: 91
    * Starting at 0x626
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x626 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x1b7

    requires s0.stack[1] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b7;
      assert s1.Peek(1) == 0xb1;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s2, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 44
    * Starting at 0x1b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb1;
      var s2 := Push2(s1, 0x01c1);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0784);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s486(s5, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 112
    * Starting at 0x784
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x1c1

    requires s0.stack[2] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c1;
      assert s1.Peek(2) == 0xb1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x1c1;
      assert s11.Peek(4) == 0xb1;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup1(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Exp(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0x1c1;
      assert s21.Peek(7) == 0xb1;
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
      assert s31.Peek(7) == 0x1c1;
      assert s31.Peek(8) == 0xb1;
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
      ExecuteFromCFGNode_s487(s41, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 113
    * Starting at 0x818
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x818 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c1

    requires s0.stack[6] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := And(s0);
      assert s1.Peek(4) == 0x1c1;
      assert s1.Peek(5) == 0xb1;
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
      assert s11.Peek(2) == 0x1c1;
      assert s11.Peek(3) == 0xb1;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s14, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 45
    * Starting at 0x1c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb1;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s2, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 18
    * Starting at 0xb1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1 as nat
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

  /** Node 490
    * Segment Id for this node is: 14
    * Starting at 0x8d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00a7);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x00a2);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0xa2;
      assert s11.Peek(3) == 0xa7;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0caa);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s14, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 205
    * Starting at 0xcaa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xa2

    requires s0.stack[3] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa2;
      assert s1.Peek(3) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cc1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s494(s11, gas - 1)
      else
        ExecuteFromCFGNode_s492(s11, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 206
    * Starting at 0xcb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xa2

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0cc0);
      assert s1.Peek(0) == 0xcc0;
      assert s1.Peek(5) == 0xa2;
      assert s1.Peek(6) == 0xa7;
      var s2 := Push2(s1, 0x09f0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s3, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 137
    * Starting at 0x9f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xcc0

    requires s0.stack[5] == 0xa2

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcc0;
      assert s1.Peek(5) == 0xa2;
      assert s1.Peek(6) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 494
    * Segment Id for this node is: 208
    * Starting at 0xcc1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xa2

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa2;
      assert s1.Peek(5) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cdf);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s497(s11, gas - 1)
      else
        ExecuteFromCFGNode_s495(s11, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 209
    * Starting at 0xcd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xa2

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0cde);
      assert s1.Peek(0) == 0xcde;
      assert s1.Peek(6) == 0xa2;
      assert s1.Peek(7) == 0xa7;
      var s2 := Push2(s1, 0x09f5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s3, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 138
    * Starting at 0x9f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xcde

    requires s0.stack[6] == 0xa2

    requires s0.stack[7] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcde;
      assert s1.Peek(6) == 0xa2;
      assert s1.Peek(7) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 497
    * Segment Id for this node is: 211
    * Starting at 0xcdf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xa2

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa2;
      assert s1.Peek(6) == 0xa7;
      var s2 := Push2(s1, 0x0ceb);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0b83);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s8, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 174
    * Starting at 0xb83
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xceb

    requires s0.stack[8] == 0xa2

    requires s0.stack[9] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xceb;
      assert s1.Peek(8) == 0xa2;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0b98);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s501(s9, gas - 1)
      else
        ExecuteFromCFGNode_s499(s9, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 175
    * Starting at 0xb90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xceb

    requires s0.stack[9] == 0xa2

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b97);
      assert s1.Peek(0) == 0xb97;
      assert s1.Peek(4) == 0xceb;
      assert s1.Peek(10) == 0xa2;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push2(s1, 0x09fa);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s3, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 139
    * Starting at 0x9fa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xb97

    requires s0.stack[4] == 0xceb

    requires s0.stack[10] == 0xa2

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb97;
      assert s1.Peek(4) == 0xceb;
      assert s1.Peek(10) == 0xa2;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 501
    * Segment Id for this node is: 177
    * Starting at 0xb98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xceb

    requires s0.stack[9] == 0xa2

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xceb;
      assert s1.Peek(9) == 0xa2;
      assert s1.Peek(10) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0ba8);
      var s5 := Dup5(s4);
      var s6 := Dup3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0b1a);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s11, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 164
    * Starting at 0xb1a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xba8

    requires s0.stack[8] == 0xceb

    requires s0.stack[14] == 0xa2

    requires s0.stack[15] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xba8;
      assert s1.Peek(8) == 0xceb;
      assert s1.Peek(14) == 0xa2;
      assert s1.Peek(15) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0b2d);
      var s4 := Push2(s3, 0x0b28);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0a8b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s7, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 150
    * Starting at 0xa8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xb28

    requires s0.stack[2] == 0xb2d

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xceb

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb28;
      assert s1.Peek(2) == 0xb2d;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xceb;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0aa6);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s506(s8, gas - 1)
      else
        ExecuteFromCFGNode_s504(s8, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 151
    * Starting at 0xa9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xb28

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xceb

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0aa5);
      assert s1.Peek(0) == 0xaa5;
      assert s1.Peek(3) == 0xb28;
      assert s1.Peek(4) == 0xb2d;
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xceb;
      assert s1.Peek(20) == 0xa2;
      assert s1.Peek(21) == 0xa7;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s3, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xaa5

    requires s0.stack[3] == 0xb28

    requires s0.stack[4] == 0xb2d

    requires s0.stack[9] == 0xba8

    requires s0.stack[14] == 0xceb

    requires s0.stack[20] == 0xa2

    requires s0.stack[21] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xaa5;
      assert s1.Peek(3) == 0xb28;
      assert s1.Peek(4) == 0xb2d;
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xceb;
      assert s1.Peek(20) == 0xa2;
      assert s1.Peek(21) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 506
    * Segment Id for this node is: 153
    * Starting at 0xaa6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xb28

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xceb

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb28;
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xceb;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0xb28;
      assert s11.Peek(3) == 0xb2d;
      assert s11.Peek(8) == 0xba8;
      assert s11.Peek(13) == 0xceb;
      assert s11.Peek(19) == 0xa2;
      assert s11.Peek(20) == 0xa7;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s507(s15, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 165
    * Starting at 0xb28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xb2d

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xceb

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2d;
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xceb;
      assert s1.Peek(17) == 0xa2;
      assert s1.Peek(18) == 0xa7;
      var s2 := Push2(s1, 0x0a70);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s508(s3, gas - 1)
  }

  /** Node 508
    * Segment Id for this node is: 147
    * Starting at 0xa70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xb2d

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xceb

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2d;
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xceb;
      assert s1.Peek(17) == 0xa2;
      assert s1.Peek(18) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0a7a);
      var s4 := Push2(s3, 0x09e6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s5, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 136
    * Starting at 0x9e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xa7a

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xceb

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa7a;
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xceb;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s8, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 148
    * Starting at 0xa7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xb2d

    requires s0.stack[8] == 0xba8

    requires s0.stack[13] == 0xceb

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb2d;
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xceb;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Push2(s6, 0x0a3f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s8, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 142
    * Starting at 0xa3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xa86

    requires s0.stack[5] == 0xb2d

    requires s0.stack[10] == 0xba8

    requires s0.stack[15] == 0xceb

    requires s0.stack[21] == 0xa2

    requires s0.stack[22] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa86;
      assert s1.Peek(5) == 0xb2d;
      assert s1.Peek(10) == 0xba8;
      assert s1.Peek(15) == 0xceb;
      assert s1.Peek(21) == 0xa2;
      assert s1.Peek(22) == 0xa7;
      var s2 := Push2(s1, 0x0a48);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09ff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s5, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 140
    * Starting at 0x9ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xa48

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xb2d

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xceb

    requires s0.stack[23] == 0xa2

    requires s0.stack[24] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa48;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xceb;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xa48;
      assert s11.Peek(5) == 0xa86;
      assert s11.Peek(8) == 0xb2d;
      assert s11.Peek(13) == 0xba8;
      assert s11.Peek(18) == 0xceb;
      assert s11.Peek(24) == 0xa2;
      assert s11.Peek(25) == 0xa7;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s14, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 143
    * Starting at 0xa48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xceb

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xb2d;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xceb;
      assert s1.Peek(22) == 0xa2;
      assert s1.Peek(23) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := Or(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(4) == 0xa86;
      assert s11.Peek(7) == 0xb2d;
      assert s11.Peek(12) == 0xba8;
      assert s11.Peek(17) == 0xceb;
      assert s11.Peek(23) == 0xa2;
      assert s11.Peek(24) == 0xa7;
      var s12 := Push2(s11, 0x0a67);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s516(s13, gas - 1)
      else
        ExecuteFromCFGNode_s514(s13, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 144
    * Starting at 0xa5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xceb

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a66);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xceb;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s3, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[0] == 0xa66

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xb2d

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xceb

    requires s0.stack[23] == 0xa2

    requires s0.stack[24] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xb2d;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xceb;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 516
    * Segment Id for this node is: 146
    * Starting at 0xa67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xb2d

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xceb

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xb2d;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xceb;
      assert s1.Peek(22) == 0xa2;
      assert s1.Peek(23) == 0xa7;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s517(s8, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 149
    * Starting at 0xa86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xb2d

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xceb

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb2d;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xceb;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s5, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 166
    * Starting at 0xb2d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xba8

    requires s0.stack[10] == 0xceb

    requires s0.stack[16] == 0xa2

    requires s0.stack[17] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xba8;
      assert s1.Peek(10) == 0xceb;
      assert s1.Peek(16) == 0xa2;
      assert s1.Peek(17) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0xba8;
      assert s11.Peek(11) == 0xceb;
      assert s11.Peek(17) == 0xa2;
      assert s11.Peek(18) == 0xa7;
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup5(s13);
      var s15 := Mul(s14);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := Dup6(s17);
      var s19 := Dup2(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0xba8;
      assert s21.Peek(12) == 0xceb;
      assert s21.Peek(18) == 0xa2;
      assert s21.Peek(19) == 0xa7;
      var s22 := Push2(s21, 0x0b50);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s521(s23, gas - 1)
      else
        ExecuteFromCFGNode_s519(s23, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 167
    * Starting at 0xb48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xceb

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0b4f);
      assert s1.Peek(0) == 0xb4f;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xceb;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Push2(s1, 0x0ab7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s3, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 154
    * Starting at 0xab7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xb4f

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xceb

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb4f;
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xceb;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 521
    * Segment Id for this node is: 169
    * Starting at 0xb50
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xba8

    requires s0.stack[11] == 0xceb

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xba8;
      assert s1.Peek(11) == 0xceb;
      assert s1.Peek(17) == 0xa2;
      assert s1.Peek(18) == 0xa7;
      var s2 := Dup4(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s522(s2, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 170
    * Starting at 0xb52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xceb

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xceb;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b79);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s534(s7, gas - 1)
      else
        ExecuteFromCFGNode_s523(s7, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 171
    * Starting at 0xb5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xceb

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xba8;
      assert s1.Peek(13) == 0xceb;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Push2(s1, 0x0b65);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0b05);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s6, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 162
    * Starting at 0xb05
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xb65

    requires s0.stack[11] == 0xba8

    requires s0.stack[16] == 0xceb

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb65;
      assert s1.Peek(11) == 0xba8;
      assert s1.Peek(16) == 0xceb;
      assert s1.Peek(22) == 0xa2;
      assert s1.Peek(23) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0b14);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0aee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s525(s10, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 158
    * Starting at 0xaee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xceb

    requires s0.stack[25] == 0xa2

    requires s0.stack[26] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xb65;
      assert s1.Peek(14) == 0xba8;
      assert s1.Peek(19) == 0xceb;
      assert s1.Peek(25) == 0xa2;
      assert s1.Peek(26) == 0xa7;
      var s2 := Push2(s1, 0x0af7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s5, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xaf7

    requires s0.stack[3] == 0xb14

    requires s0.stack[7] == 0xb65

    requires s0.stack[16] == 0xba8

    requires s0.stack[21] == 0xceb

    requires s0.stack[27] == 0xa2

    requires s0.stack[28] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaf7;
      assert s1.Peek(3) == 0xb14;
      assert s1.Peek(7) == 0xb65;
      assert s1.Peek(16) == 0xba8;
      assert s1.Peek(21) == 0xceb;
      assert s1.Peek(27) == 0xa2;
      assert s1.Peek(28) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s6, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xaf7

    requires s0.stack[6] == 0xb14

    requires s0.stack[10] == 0xb65

    requires s0.stack[19] == 0xba8

    requires s0.stack[24] == 0xceb

    requires s0.stack[30] == 0xa2

    requires s0.stack[31] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xaf7;
      assert s1.Peek(6) == 0xb14;
      assert s1.Peek(10) == 0xb65;
      assert s1.Peek(19) == 0xba8;
      assert s1.Peek(24) == 0xceb;
      assert s1.Peek(30) == 0xa2;
      assert s1.Peek(31) == 0xa7;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s528(s11, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0xaf7

    requires s0.stack[5] == 0xb14

    requires s0.stack[9] == 0xb65

    requires s0.stack[18] == 0xba8

    requires s0.stack[23] == 0xceb

    requires s0.stack[29] == 0xa2

    requires s0.stack[30] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaf7;
      assert s1.Peek(5) == 0xb14;
      assert s1.Peek(9) == 0xb65;
      assert s1.Peek(18) == 0xba8;
      assert s1.Peek(23) == 0xceb;
      assert s1.Peek(29) == 0xa2;
      assert s1.Peek(30) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s7, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 159
    * Starting at 0xaf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0xb14

    requires s0.stack[6] == 0xb65

    requires s0.stack[15] == 0xba8

    requires s0.stack[20] == 0xceb

    requires s0.stack[26] == 0xa2

    requires s0.stack[27] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xb65;
      assert s1.Peek(15) == 0xba8;
      assert s1.Peek(20) == 0xceb;
      assert s1.Peek(26) == 0xa2;
      assert s1.Peek(27) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0b02);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s531(s5, gas - 1)
      else
        ExecuteFromCFGNode_s530(s5, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 160
    * Starting at 0xafe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xceb

    requires s0.stack[25] == 0xa2

    requires s0.stack[26] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xb14;
      assert s1.Peek(6) == 0xb65;
      assert s1.Peek(15) == 0xba8;
      assert s1.Peek(20) == 0xceb;
      assert s1.Peek(26) == 0xa2;
      assert s1.Peek(27) == 0xa7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 531
    * Segment Id for this node is: 161
    * Starting at 0xb02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xb14

    requires s0.stack[5] == 0xb65

    requires s0.stack[14] == 0xba8

    requires s0.stack[19] == 0xceb

    requires s0.stack[25] == 0xa2

    requires s0.stack[26] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb14;
      assert s1.Peek(5) == 0xb65;
      assert s1.Peek(14) == 0xba8;
      assert s1.Peek(19) == 0xceb;
      assert s1.Peek(25) == 0xa2;
      assert s1.Peek(26) == 0xa7;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s3, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 163
    * Starting at 0xb14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xb65

    requires s0.stack[12] == 0xba8

    requires s0.stack[17] == 0xceb

    requires s0.stack[23] == 0xa2

    requires s0.stack[24] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb65;
      assert s1.Peek(12) == 0xba8;
      assert s1.Peek(17) == 0xceb;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s533(s6, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 172
    * Starting at 0xb65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0xba8

    requires s0.stack[14] == 0xceb

    requires s0.stack[20] == 0xa2

    requires s0.stack[21] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xba8;
      assert s1.Peek(14) == 0xceb;
      assert s1.Peek(20) == 0xa2;
      assert s1.Peek(21) == 0xa7;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0xba8;
      assert s11.Peek(14) == 0xceb;
      assert s11.Peek(20) == 0xa2;
      assert s11.Peek(21) == 0xa7;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0b52);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s16, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 173
    * Starting at 0xb79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xba8

    requires s0.stack[12] == 0xceb

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xba8;
      assert s1.Peek(12) == 0xceb;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s10, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 178
    * Starting at 0xba8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xceb

    requires s0.stack[11] == 0xa2

    requires s0.stack[12] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xceb;
      assert s1.Peek(11) == 0xa2;
      assert s1.Peek(12) == 0xa7;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s9, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 212
    * Starting at 0xceb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xceb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xa2

    requires s0.stack[7] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xa2;
      assert s1.Peek(7) == 0xa7;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push8(s8, 0xffffffffffffffff);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0xa2;
      assert s11.Peek(7) == 0xa7;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0d0c);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s539(s14, gas - 1)
      else
        ExecuteFromCFGNode_s537(s14, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 213
    * Starting at 0xd04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xa2

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d0b);
      assert s1.Peek(0) == 0xd0b;
      assert s1.Peek(6) == 0xa2;
      assert s1.Peek(7) == 0xa7;
      var s2 := Push2(s1, 0x09f5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s3, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 138
    * Starting at 0x9f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xd0b

    requires s0.stack[6] == 0xa2

    requires s0.stack[7] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd0b;
      assert s1.Peek(6) == 0xa2;
      assert s1.Peek(7) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 539
    * Segment Id for this node is: 215
    * Starting at 0xd0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xa2

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xa2;
      assert s1.Peek(6) == 0xa7;
      var s2 := Push2(s1, 0x0d18);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0c7c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s8, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 200
    * Starting at 0xc7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xd18

    requires s0.stack[8] == 0xa2

    requires s0.stack[9] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd18;
      assert s1.Peek(8) == 0xa2;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0c91);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s543(s9, gas - 1)
      else
        ExecuteFromCFGNode_s541(s9, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 201
    * Starting at 0xc89
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd18

    requires s0.stack[9] == 0xa2

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0c90);
      assert s1.Peek(0) == 0xc90;
      assert s1.Peek(4) == 0xd18;
      assert s1.Peek(10) == 0xa2;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push2(s1, 0x09fa);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s3, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 139
    * Starting at 0x9fa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xc90

    requires s0.stack[4] == 0xd18

    requires s0.stack[10] == 0xa2

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc90;
      assert s1.Peek(4) == 0xd18;
      assert s1.Peek(10) == 0xa2;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 543
    * Segment Id for this node is: 203
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd18

    requires s0.stack[9] == 0xa2

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd18;
      assert s1.Peek(9) == 0xa2;
      assert s1.Peek(10) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0ca1);
      var s5 := Dup5(s4);
      var s6 := Dup3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c13);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s11, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 190
    * Starting at 0xc13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xca1

    requires s0.stack[8] == 0xd18

    requires s0.stack[14] == 0xa2

    requires s0.stack[15] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xca1;
      assert s1.Peek(8) == 0xd18;
      assert s1.Peek(14) == 0xa2;
      assert s1.Peek(15) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0c26);
      var s4 := Push2(s3, 0x0c21);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0bb1);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s7, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 179
    * Starting at 0xbb1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xc21

    requires s0.stack[2] == 0xc26

    requires s0.stack[7] == 0xca1

    requires s0.stack[12] == 0xd18

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc21;
      assert s1.Peek(2) == 0xc26;
      assert s1.Peek(7) == 0xca1;
      assert s1.Peek(12) == 0xd18;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0bcc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s548(s8, gas - 1)
      else
        ExecuteFromCFGNode_s546(s8, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 180
    * Starting at 0xbc4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xc21

    requires s0.stack[3] == 0xc26

    requires s0.stack[8] == 0xca1

    requires s0.stack[13] == 0xd18

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0bcb);
      assert s1.Peek(0) == 0xbcb;
      assert s1.Peek(3) == 0xc21;
      assert s1.Peek(4) == 0xc26;
      assert s1.Peek(9) == 0xca1;
      assert s1.Peek(14) == 0xd18;
      assert s1.Peek(20) == 0xa2;
      assert s1.Peek(21) == 0xa7;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s3, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xbcb

    requires s0.stack[3] == 0xc21

    requires s0.stack[4] == 0xc26

    requires s0.stack[9] == 0xca1

    requires s0.stack[14] == 0xd18

    requires s0.stack[20] == 0xa2

    requires s0.stack[21] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xbcb;
      assert s1.Peek(3) == 0xc21;
      assert s1.Peek(4) == 0xc26;
      assert s1.Peek(9) == 0xca1;
      assert s1.Peek(14) == 0xd18;
      assert s1.Peek(20) == 0xa2;
      assert s1.Peek(21) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 548
    * Segment Id for this node is: 182
    * Starting at 0xbcc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xc21

    requires s0.stack[3] == 0xc26

    requires s0.stack[8] == 0xca1

    requires s0.stack[13] == 0xd18

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc21;
      assert s1.Peek(3) == 0xc26;
      assert s1.Peek(8) == 0xca1;
      assert s1.Peek(13) == 0xd18;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0xc21;
      assert s11.Peek(3) == 0xc26;
      assert s11.Peek(8) == 0xca1;
      assert s11.Peek(13) == 0xd18;
      assert s11.Peek(19) == 0xa2;
      assert s11.Peek(20) == 0xa7;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s15, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 191
    * Starting at 0xc21
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xc26

    requires s0.stack[6] == 0xca1

    requires s0.stack[11] == 0xd18

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc26;
      assert s1.Peek(6) == 0xca1;
      assert s1.Peek(11) == 0xd18;
      assert s1.Peek(17) == 0xa2;
      assert s1.Peek(18) == 0xa7;
      var s2 := Push2(s1, 0x0a70);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s3, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 147
    * Starting at 0xa70
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xc26

    requires s0.stack[6] == 0xca1

    requires s0.stack[11] == 0xd18

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc26;
      assert s1.Peek(6) == 0xca1;
      assert s1.Peek(11) == 0xd18;
      assert s1.Peek(17) == 0xa2;
      assert s1.Peek(18) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0a7a);
      var s4 := Push2(s3, 0x09e6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s551(s5, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 136
    * Starting at 0x9e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xa7a

    requires s0.stack[3] == 0xc26

    requires s0.stack[8] == 0xca1

    requires s0.stack[13] == 0xd18

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa7a;
      assert s1.Peek(3) == 0xc26;
      assert s1.Peek(8) == 0xca1;
      assert s1.Peek(13) == 0xd18;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s552(s8, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 148
    * Starting at 0xa7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xc26

    requires s0.stack[8] == 0xca1

    requires s0.stack[13] == 0xd18

    requires s0.stack[19] == 0xa2

    requires s0.stack[20] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc26;
      assert s1.Peek(8) == 0xca1;
      assert s1.Peek(13) == 0xd18;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0a86);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Push2(s6, 0x0a3f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s553(s8, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 142
    * Starting at 0xa3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xa86

    requires s0.stack[5] == 0xc26

    requires s0.stack[10] == 0xca1

    requires s0.stack[15] == 0xd18

    requires s0.stack[21] == 0xa2

    requires s0.stack[22] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa86;
      assert s1.Peek(5) == 0xc26;
      assert s1.Peek(10) == 0xca1;
      assert s1.Peek(15) == 0xd18;
      assert s1.Peek(21) == 0xa2;
      assert s1.Peek(22) == 0xa7;
      var s2 := Push2(s1, 0x0a48);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09ff);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s5, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 140
    * Starting at 0x9ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[1] == 0xa48

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xc26

    requires s0.stack[12] == 0xca1

    requires s0.stack[17] == 0xd18

    requires s0.stack[23] == 0xa2

    requires s0.stack[24] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa48;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xc26;
      assert s1.Peek(12) == 0xca1;
      assert s1.Peek(17) == 0xd18;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xa48;
      assert s11.Peek(5) == 0xa86;
      assert s11.Peek(8) == 0xc26;
      assert s11.Peek(13) == 0xca1;
      assert s11.Peek(18) == 0xd18;
      assert s11.Peek(24) == 0xa2;
      assert s11.Peek(25) == 0xa7;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s555(s14, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 143
    * Starting at 0xa48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xc26

    requires s0.stack[11] == 0xca1

    requires s0.stack[16] == 0xd18

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xc26;
      assert s1.Peek(11) == 0xca1;
      assert s1.Peek(16) == 0xd18;
      assert s1.Peek(22) == 0xa2;
      assert s1.Peek(23) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup3(s7);
      var s9 := Gt(s8);
      var s10 := Or(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(4) == 0xa86;
      assert s11.Peek(7) == 0xc26;
      assert s11.Peek(12) == 0xca1;
      assert s11.Peek(17) == 0xd18;
      assert s11.Peek(23) == 0xa2;
      assert s11.Peek(24) == 0xa7;
      var s12 := Push2(s11, 0x0a67);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s558(s13, gas - 1)
      else
        ExecuteFromCFGNode_s556(s13, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 144
    * Starting at 0xa5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xc26

    requires s0.stack[11] == 0xca1

    requires s0.stack[16] == 0xd18

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a66);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xc26;
      assert s1.Peek(12) == 0xca1;
      assert s1.Peek(17) == 0xd18;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Push2(s1, 0x0a10);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s3, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 141
    * Starting at 0xa10
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[0] == 0xa66

    requires s0.stack[4] == 0xa86

    requires s0.stack[7] == 0xc26

    requires s0.stack[12] == 0xca1

    requires s0.stack[17] == 0xd18

    requires s0.stack[23] == 0xa2

    requires s0.stack[24] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa66;
      assert s1.Peek(4) == 0xa86;
      assert s1.Peek(7) == 0xc26;
      assert s1.Peek(12) == 0xca1;
      assert s1.Peek(17) == 0xd18;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x41);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 558
    * Segment Id for this node is: 146
    * Starting at 0xa67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[3] == 0xa86

    requires s0.stack[6] == 0xc26

    requires s0.stack[11] == 0xca1

    requires s0.stack[16] == 0xd18

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa86;
      assert s1.Peek(6) == 0xc26;
      assert s1.Peek(11) == 0xca1;
      assert s1.Peek(16) == 0xd18;
      assert s1.Peek(22) == 0xa2;
      assert s1.Peek(23) == 0xa7;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s8, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 149
    * Starting at 0xa86
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xc26

    requires s0.stack[7] == 0xca1

    requires s0.stack[12] == 0xd18

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc26;
      assert s1.Peek(7) == 0xca1;
      assert s1.Peek(12) == 0xd18;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s560(s5, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 192
    * Starting at 0xc26
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xca1

    requires s0.stack[10] == 0xd18

    requires s0.stack[16] == 0xa2

    requires s0.stack[17] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xca1;
      assert s1.Peek(10) == 0xd18;
      assert s1.Peek(16) == 0xa2;
      assert s1.Peek(17) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0xca1;
      assert s11.Peek(11) == 0xd18;
      assert s11.Peek(17) == 0xa2;
      assert s11.Peek(18) == 0xa7;
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup5(s13);
      var s15 := Mul(s14);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := Dup6(s17);
      var s19 := Dup2(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0xca1;
      assert s21.Peek(12) == 0xd18;
      assert s21.Peek(18) == 0xa2;
      assert s21.Peek(19) == 0xa7;
      var s22 := Push2(s21, 0x0c49);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s563(s23, gas - 1)
      else
        ExecuteFromCFGNode_s561(s23, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 193
    * Starting at 0xc41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xca1

    requires s0.stack[11] == 0xd18

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0c48);
      assert s1.Peek(0) == 0xc48;
      assert s1.Peek(7) == 0xca1;
      assert s1.Peek(12) == 0xd18;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Push2(s1, 0x0ab7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s3, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 154
    * Starting at 0xab7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xc48

    requires s0.stack[7] == 0xca1

    requires s0.stack[12] == 0xd18

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc48;
      assert s1.Peek(7) == 0xca1;
      assert s1.Peek(12) == 0xd18;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 563
    * Segment Id for this node is: 195
    * Starting at 0xc49
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xca1

    requires s0.stack[11] == 0xd18

    requires s0.stack[17] == 0xa2

    requires s0.stack[18] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xca1;
      assert s1.Peek(11) == 0xd18;
      assert s1.Peek(17) == 0xa2;
      assert s1.Peek(18) == 0xa7;
      var s2 := Dup4(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s564(s2, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 196
    * Starting at 0xc4b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xca1

    requires s0.stack[12] == 0xd18

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xca1;
      assert s1.Peek(12) == 0xd18;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c72);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s574(s7, gas - 1)
      else
        ExecuteFromCFGNode_s565(s7, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 197
    * Starting at 0xc54
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xca1

    requires s0.stack[12] == 0xd18

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xca1;
      assert s1.Peek(13) == 0xd18;
      assert s1.Peek(19) == 0xa2;
      assert s1.Peek(20) == 0xa7;
      var s2 := Push2(s1, 0x0c5e);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0bfe);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s6, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 188
    * Starting at 0xbfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xc5e

    requires s0.stack[11] == 0xca1

    requires s0.stack[16] == 0xd18

    requires s0.stack[22] == 0xa2

    requires s0.stack[23] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc5e;
      assert s1.Peek(11) == 0xca1;
      assert s1.Peek(16) == 0xd18;
      assert s1.Peek(22) == 0xa2;
      assert s1.Peek(23) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c0d);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0be7);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s10, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 184
    * Starting at 0xbe7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xc0d

    requires s0.stack[5] == 0xc5e

    requires s0.stack[14] == 0xca1

    requires s0.stack[19] == 0xd18

    requires s0.stack[25] == 0xa2

    requires s0.stack[26] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc0d;
      assert s1.Peek(5) == 0xc5e;
      assert s1.Peek(14) == 0xca1;
      assert s1.Peek(19) == 0xd18;
      assert s1.Peek(25) == 0xa2;
      assert s1.Peek(26) == 0xa7;
      var s2 := Push2(s1, 0x0bf0);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s568(s5, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0xbf0

    requires s0.stack[3] == 0xc0d

    requires s0.stack[7] == 0xc5e

    requires s0.stack[16] == 0xca1

    requires s0.stack[21] == 0xd18

    requires s0.stack[27] == 0xa2

    requires s0.stack[28] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbf0;
      assert s1.Peek(3) == 0xc0d;
      assert s1.Peek(7) == 0xc5e;
      assert s1.Peek(16) == 0xca1;
      assert s1.Peek(21) == 0xd18;
      assert s1.Peek(27) == 0xa2;
      assert s1.Peek(28) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s9, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 185
    * Starting at 0xbf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0xc0d

    requires s0.stack[6] == 0xc5e

    requires s0.stack[15] == 0xca1

    requires s0.stack[20] == 0xd18

    requires s0.stack[26] == 0xa2

    requires s0.stack[27] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc0d;
      assert s1.Peek(6) == 0xc5e;
      assert s1.Peek(15) == 0xca1;
      assert s1.Peek(20) == 0xd18;
      assert s1.Peek(26) == 0xa2;
      assert s1.Peek(27) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0bfb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s571(s5, gas - 1)
      else
        ExecuteFromCFGNode_s570(s5, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 186
    * Starting at 0xbf7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xc0d

    requires s0.stack[5] == 0xc5e

    requires s0.stack[14] == 0xca1

    requires s0.stack[19] == 0xd18

    requires s0.stack[25] == 0xa2

    requires s0.stack[26] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xc0d;
      assert s1.Peek(6) == 0xc5e;
      assert s1.Peek(15) == 0xca1;
      assert s1.Peek(20) == 0xd18;
      assert s1.Peek(26) == 0xa2;
      assert s1.Peek(27) == 0xa7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 571
    * Segment Id for this node is: 187
    * Starting at 0xbfb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0xc0d

    requires s0.stack[5] == 0xc5e

    requires s0.stack[14] == 0xca1

    requires s0.stack[19] == 0xd18

    requires s0.stack[25] == 0xa2

    requires s0.stack[26] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc0d;
      assert s1.Peek(5) == 0xc5e;
      assert s1.Peek(14) == 0xca1;
      assert s1.Peek(19) == 0xd18;
      assert s1.Peek(25) == 0xa2;
      assert s1.Peek(26) == 0xa7;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s572(s3, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 189
    * Starting at 0xc0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0xc5e

    requires s0.stack[12] == 0xca1

    requires s0.stack[17] == 0xd18

    requires s0.stack[23] == 0xa2

    requires s0.stack[24] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc5e;
      assert s1.Peek(12) == 0xca1;
      assert s1.Peek(17) == 0xd18;
      assert s1.Peek(23) == 0xa2;
      assert s1.Peek(24) == 0xa7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s573(s6, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 198
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0xca1

    requires s0.stack[14] == 0xd18

    requires s0.stack[20] == 0xa2

    requires s0.stack[21] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xca1;
      assert s1.Peek(14) == 0xd18;
      assert s1.Peek(20) == 0xa2;
      assert s1.Peek(21) == 0xa7;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0xca1;
      assert s11.Peek(14) == 0xd18;
      assert s11.Peek(20) == 0xa2;
      assert s11.Peek(21) == 0xa7;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Push2(s14, 0x0c4b);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s16, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 199
    * Starting at 0xc72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0xca1

    requires s0.stack[12] == 0xd18

    requires s0.stack[18] == 0xa2

    requires s0.stack[19] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xca1;
      assert s1.Peek(12) == 0xd18;
      assert s1.Peek(18) == 0xa2;
      assert s1.Peek(19) == 0xa7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s575(s10, gas - 1)
  }

  /** Node 575
    * Segment Id for this node is: 204
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd18

    requires s0.stack[11] == 0xa2

    requires s0.stack[12] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd18;
      assert s1.Peek(11) == 0xa2;
      assert s1.Peek(12) == 0xa7;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s576(s9, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 216
    * Starting at 0xd18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xa2

    requires s0.stack[7] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xa2;
      assert s1.Peek(7) == 0xa7;
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
      ExecuteFromCFGNode_s577(s10, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 15
    * Starting at 0xa2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa7;
      var s2 := Push2(s1, 0x0199);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s578(s3, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 40
    * Starting at 0x199
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x199 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa7;
      var s2 := Push2(s1, 0x01a1);
      var s3 := Push2(s2, 0x05a1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s579(s4, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 85
    * Starting at 0x5a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x1a1

    requires s0.stack[3] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a1;
      assert s1.Peek(3) == 0xa7;
      var s2 := Push2(s1, 0x05a9);
      var s3 := Push2(s2, 0x09de);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s580(s4, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5a9

    requires s0.stack[1] == 0x1a1

    requires s0.stack[4] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5a9;
      assert s1.Peek(1) == 0x1a1;
      assert s1.Peek(4) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s581(s7, gas - 1)
  }

  /** Node 581
    * Segment Id for this node is: 86
    * Starting at 0x5a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x1a1

    requires s0.stack[4] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1a1;
      assert s1.Peek(4) == 0xa7;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x05c7);
      var s5 := Push2(s4, 0x01c3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s582(s6, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 46
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x5c7

    requires s0.stack[2] == 0x1a1

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5c7;
      assert s1.Peek(2) == 0x1a1;
      assert s1.Peek(5) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(2) == 0x5c7;
      assert s11.Peek(4) == 0x1a1;
      assert s11.Peek(7) == 0xa7;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s583(s17, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 87
    * Starting at 0x5c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x1a1

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1a1;
      assert s1.Peek(5) == 0xa7;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0626);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s595(s6, gas - 1)
      else
        ExecuteFromCFGNode_s584(s6, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 88
    * Starting at 0x5e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x1a1

    requires s0.stack[3] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x05ea);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x1a1;
      assert s1.Peek(4) == 0xa7;
      var s2 := Push2(s1, 0x09de);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s585(s3, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 135
    * Starting at 0x9de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x5ea

    requires s0.stack[1] == 0x1a1

    requires s0.stack[4] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5ea;
      assert s1.Peek(1) == 0x1a1;
      assert s1.Peek(4) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s586(s7, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 89
    * Starting at 0x5ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x1a1

    requires s0.stack[4] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1a1;
      assert s1.Peek(4) == 0xa7;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x118cdaa700000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x061d);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x61d;
      assert s11.Peek(3) == 0x1a1;
      assert s11.Peek(6) == 0xa7;
      var s12 := Push2(s11, 0x0d31);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s587(s13, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 219
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x61d

    requires s0.stack[3] == 0x1a1

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x61d;
      assert s1.Peek(3) == 0x1a1;
      assert s1.Peek(6) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d46);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd46;
      assert s11.Peek(5) == 0x61d;
      assert s11.Peek(6) == 0x1a1;
      assert s11.Peek(9) == 0xa7;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d22);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s588(s14, gas - 1)
  }

  /** Node 588
    * Segment Id for this node is: 217
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd46

    requires s0.stack[6] == 0x61d

    requires s0.stack[7] == 0x1a1

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd46;
      assert s1.Peek(6) == 0x61d;
      assert s1.Peek(7) == 0x1a1;
      assert s1.Peek(10) == 0xa7;
      var s2 := Push2(s1, 0x0d2b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0adc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s589(s5, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 156
    * Starting at 0xadc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xd2b

    requires s0.stack[4] == 0xd46

    requires s0.stack[8] == 0x61d

    requires s0.stack[9] == 0x1a1

    requires s0.stack[12] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2b;
      assert s1.Peek(4) == 0xd46;
      assert s1.Peek(8) == 0x61d;
      assert s1.Peek(9) == 0x1a1;
      assert s1.Peek(12) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0ae7);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0abc);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s6, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 155
    * Starting at 0xabc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xae7

    requires s0.stack[4] == 0xd2b

    requires s0.stack[7] == 0xd46

    requires s0.stack[11] == 0x61d

    requires s0.stack[12] == 0x1a1

    requires s0.stack[15] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae7;
      assert s1.Peek(4) == 0xd2b;
      assert s1.Peek(7) == 0xd46;
      assert s1.Peek(11) == 0x61d;
      assert s1.Peek(12) == 0x1a1;
      assert s1.Peek(15) == 0xa7;
      var s2 := Push1(s1, 0x00);
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
      ExecuteFromCFGNode_s591(s11, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 157
    * Starting at 0xae7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xd2b

    requires s0.stack[6] == 0xd46

    requires s0.stack[10] == 0x61d

    requires s0.stack[11] == 0x1a1

    requires s0.stack[14] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2b;
      assert s1.Peek(6) == 0xd46;
      assert s1.Peek(10) == 0x61d;
      assert s1.Peek(11) == 0x1a1;
      assert s1.Peek(14) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s7, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 218
    * Starting at 0xd2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd46

    requires s0.stack[7] == 0x61d

    requires s0.stack[8] == 0x1a1

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd46;
      assert s1.Peek(7) == 0x61d;
      assert s1.Peek(8) == 0x1a1;
      assert s1.Peek(11) == 0xa7;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s593(s6, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 220
    * Starting at 0xd46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x61d

    requires s0.stack[4] == 0x1a1

    requires s0.stack[7] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x61d;
      assert s1.Peek(4) == 0x1a1;
      assert s1.Peek(7) == 0xa7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s6, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 90
    * Starting at 0x61d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x1a1

    requires s0.stack[4] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1a1;
      assert s1.Peek(4) == 0xa7;
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

  /** Node 595
    * Segment Id for this node is: 91
    * Starting at 0x626
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x626 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x1a1

    requires s0.stack[3] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1a1;
      assert s1.Peek(3) == 0xa7;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s596(s2, gas - 1)
  }

  /** Node 596
    * Segment Id for this node is: 41
    * Starting at 0x1a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa7;
      var s2 := Push2(s1, 0x01ab);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0628);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s597(s6, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 92
    * Starting at 0x628
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x628 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x1ab

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ab;
      assert s1.Peek(5) == 0xa7;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Dup3(s3);
      var s5 := MLoad(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x066c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s607(s8, gas - 1)
      else
        ExecuteFromCFGNode_s598(s8, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 93
    * Starting at 0x632
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x1ab

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x1ab;
      assert s1.Peek(6) == 0xa7;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0663);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x11a3);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s599(s11, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 317
    * Starting at 0x11a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x663

    requires s0.stack[4] == 0x1ab

    requires s0.stack[7] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x663;
      assert s1.Peek(4) == 0x1ab;
      assert s1.Peek(7) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x663;
      assert s11.Peek(7) == 0x1ab;
      assert s11.Peek(10) == 0xa7;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11bc);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1180);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s18, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 314
    * Starting at 0x1180
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1180 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x11bc

    requires s0.stack[4] == 0x663

    requires s0.stack[7] == 0x1ab

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11bc;
      assert s1.Peek(4) == 0x663;
      assert s1.Peek(7) == 0x1ab;
      assert s1.Peek(10) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x118d);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x10da);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s601(s7, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 306
    * Starting at 0x10da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x118d

    requires s0.stack[5] == 0x11bc

    requires s0.stack[8] == 0x663

    requires s0.stack[11] == 0x1ab

    requires s0.stack[14] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x118d;
      assert s1.Peek(5) == 0x11bc;
      assert s1.Peek(8) == 0x663;
      assert s1.Peek(11) == 0x1ab;
      assert s1.Peek(14) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x118d;
      assert s11.Peek(6) == 0x11bc;
      assert s11.Peek(9) == 0x663;
      assert s11.Peek(12) == 0x1ab;
      assert s11.Peek(15) == 0xa7;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s15, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 315
    * Starting at 0x118d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x11bc

    requires s0.stack[6] == 0x663

    requires s0.stack[9] == 0x1ab

    requires s0.stack[12] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11bc;
      assert s1.Peek(6) == 0x663;
      assert s1.Peek(9) == 0x1ab;
      assert s1.Peek(12) == 0xa7;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1198);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1157);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s603(s7, gas - 1)
  }

  /** Node 603
    * Segment Id for this node is: 313
    * Starting at 0x1157
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1198

    requires s0.stack[4] == 0x11bc

    requires s0.stack[7] == 0x663

    requires s0.stack[10] == 0x1ab

    requires s0.stack[13] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1198;
      assert s1.Peek(4) == 0x11bc;
      assert s1.Peek(7) == 0x663;
      assert s1.Peek(10) == 0x1ab;
      assert s1.Peek(13) == 0xa7;
      var s2 := Push32(s1, 0x617272617920706172616d65746572732073686f756c6420626520657175616c);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s604(s8, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 316
    * Starting at 0x1198
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x11bc

    requires s0.stack[5] == 0x663

    requires s0.stack[8] == 0x1ab

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11bc;
      assert s1.Peek(5) == 0x663;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(11) == 0xa7;
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
      ExecuteFromCFGNode_s605(s10, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 318
    * Starting at 0x11bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x663

    requires s0.stack[6] == 0x1ab

    requires s0.stack[9] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x663;
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(9) == 0xa7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s606(s7, gas - 1)
  }

  /** Node 606
    * Segment Id for this node is: 94
    * Starting at 0x663
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x663 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1ab

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ab;
      assert s1.Peek(6) == 0xa7;
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

  /** Node 607
    * Segment Id for this node is: 95
    * Starting at 0x66c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x1ab

    requires s0.stack[5] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ab;
      assert s1.Peek(5) == 0xa7;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s608(s2, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 96
    * Starting at 0x66f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1ab

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ab;
      assert s1.Peek(6) == 0xa7;
      var s2 := Dup3(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x077f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s628(s8, gas - 1)
      else
        ExecuteFromCFGNode_s609(s8, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 97
    * Starting at 0x679
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x679 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1ab

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x1ab;
      assert s1.Peek(7) == 0xa7;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x068b);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s612(s8, gas - 1)
      else
        ExecuteFromCFGNode_s610(s8, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 98
    * Starting at 0x683
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x1ab

    requires s0.stack[8] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x068a);
      assert s1.Peek(0) == 0x68a;
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s611(s3, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x68a

    requires s0.stack[6] == 0x1ab

    requires s0.stack[9] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x68a;
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 612
    * Segment Id for this node is: 100
    * Starting at 0x68b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x1ab

    requires s0.stack[8] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ab;
      assert s1.Peek(8) == 0xa7;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x02);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup6(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(8) == 0x1ab;
      assert s11.Peek(11) == 0xa7;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x06aa);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s615(s17, gas - 1)
      else
        ExecuteFromCFGNode_s613(s17, gas - 1)
  }

  /** Node 613
    * Segment Id for this node is: 101
    * Starting at 0x6a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x1ab

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06a9);
      assert s1.Peek(0) == 0x6a9;
      assert s1.Peek(9) == 0x1ab;
      assert s1.Peek(12) == 0xa7;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s614(s3, gas - 1)
  }

  /** Node 614
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6a9

    requires s0.stack[9] == 0x1ab

    requires s0.stack[12] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6a9;
      assert s1.Peek(9) == 0x1ab;
      assert s1.Peek(12) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 615
    * Segment Id for this node is: 103
    * Starting at 0x6aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x1ab

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x1ab;
      assert s11.Peek(10) == 0xa7;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(6) == 0x1ab;
      assert s21.Peek(9) == 0xa7;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup3(s26);
      var s28 := Dup2(s27);
      var s29 := Dup2(s28);
      var s30 := MLoad(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(7) == 0x1ab;
      assert s31.Peek(10) == 0xa7;
      var s32 := Lt(s31);
      var s33 := Push2(s32, 0x0703);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s618(s34, gas - 1)
      else
        ExecuteFromCFGNode_s616(s34, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 104
    * Starting at 0x6fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x1ab

    requires s0.stack[8] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0702);
      assert s1.Peek(0) == 0x702;
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s617(s3, gas - 1)
  }

  /** Node 617
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x702

    requires s0.stack[6] == 0x1ab

    requires s0.stack[9] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x702;
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 618
    * Segment Id for this node is: 106
    * Starting at 0x703
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x1ab

    requires s0.stack[8] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ab;
      assert s1.Peek(8) == 0xa7;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push32(s9, 0x041c2475f26c9b591c9f1c0705a40a15906fbf6d247cdf00adac71dee71750c4);
      var s11 := Dup4(s10);
      assert s11.Peek(6) == 0x1ab;
      assert s11.Peek(9) == 0xa7;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MLoad(s13);
      var s15 := Dup2(s14);
      var s16 := Lt(s15);
      var s17 := Push2(s16, 0x0755);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s621(s18, gas - 1)
      else
        ExecuteFromCFGNode_s619(s18, gas - 1)
  }

  /** Node 619
    * Segment Id for this node is: 107
    * Starting at 0x74d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x1ab

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0754);
      assert s1.Peek(0) == 0x754;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push2(s1, 0x0fa3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s620(s3, gas - 1)
  }

  /** Node 620
    * Segment Id for this node is: 280
    * Starting at 0xfa3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x754

    requires s0.stack[8] == 0x1ab

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x754;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 621
    * Segment Id for this node is: 109
    * Starting at 0x755
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x755 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x1ab

    requires s0.stack[10] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1ab;
      assert s1.Peek(10) == 0xa7;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Push2(s9, 0x076a);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x76a;
      assert s11.Peek(8) == 0x1ab;
      assert s11.Peek(11) == 0xa7;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0f88);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s622(s14, gas - 1)
  }

  /** Node 622
    * Segment Id for this node is: 278
    * Starting at 0xf88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x76a

    requires s0.stack[8] == 0x1ab

    requires s0.stack[11] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x76a;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(11) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0f9d);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xf9d;
      assert s11.Peek(5) == 0x76a;
      assert s11.Peek(11) == 0x1ab;
      assert s11.Peek(14) == 0xa7;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0f79);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s623(s14, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 276
    * Starting at 0xf79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xf9d

    requires s0.stack[6] == 0x76a

    requires s0.stack[12] == 0x1ab

    requires s0.stack[15] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9d;
      assert s1.Peek(6) == 0x76a;
      assert s1.Peek(12) == 0x1ab;
      assert s1.Peek(15) == 0xa7;
      var s2 := Push2(s1, 0x0f82);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0bdd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s624(s5, gas - 1)
  }

  /** Node 624
    * Segment Id for this node is: 183
    * Starting at 0xbdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf82

    requires s0.stack[4] == 0xf9d

    requires s0.stack[8] == 0x76a

    requires s0.stack[14] == 0x1ab

    requires s0.stack[17] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf82;
      assert s1.Peek(4) == 0xf9d;
      assert s1.Peek(8) == 0x76a;
      assert s1.Peek(14) == 0x1ab;
      assert s1.Peek(17) == 0xa7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s625(s9, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 277
    * Starting at 0xf82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xf9d

    requires s0.stack[7] == 0x76a

    requires s0.stack[13] == 0x1ab

    requires s0.stack[16] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9d;
      assert s1.Peek(7) == 0x76a;
      assert s1.Peek(13) == 0x1ab;
      assert s1.Peek(16) == 0xa7;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s626(s6, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 279
    * Starting at 0xf9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x76a

    requires s0.stack[9] == 0x1ab

    requires s0.stack[12] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x76a;
      assert s1.Peek(9) == 0x1ab;
      assert s1.Peek(12) == 0xa7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s627(s6, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 110
    * Starting at 0x76a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x1ab

    requires s0.stack[9] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(9) == 0xa7;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log2(s7);
      var s9 := Dup1(s8);
      var s10 := Dup1(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x1ab;
      assert s11.Peek(9) == 0xa7;
      var s12 := Add(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Push2(s15, 0x066f);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s608(s17, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 111
    * Starting at 0x77f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1ab

    requires s0.stack[6] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ab;
      assert s1.Peek(6) == 0xa7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s629(s5, gas - 1)
  }

  /** Node 629
    * Segment Id for this node is: 42
    * Starting at 0x1ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xa7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s630(s4, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 16
    * Starting at 0xa7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
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

  /** Node 631
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
