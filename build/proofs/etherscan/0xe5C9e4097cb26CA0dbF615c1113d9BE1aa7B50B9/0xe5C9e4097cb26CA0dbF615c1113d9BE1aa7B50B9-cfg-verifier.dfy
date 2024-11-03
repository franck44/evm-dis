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
      var s1 := Push20(s0, 0xe5c9e4097cb26ca0dbf615c1113d9be1aa7b50b9);
      var s2 := Address(s1);
      var s3 := Eq(s2);
      var s4 := Push1(s3, 0x80);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := CallDataSize(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x006c);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s11, gas - 1)
      else
        ExecuteFromCFGNode_s1(s11, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x24
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x17e142d1);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0071);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s9, gas - 1)
      else
        ExecuteFromCFGNode_s2(s9, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x4c60db9c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0097);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x40
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x732a2ccf);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00b9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x4b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xbc2b405c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00e6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x56
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xd1aa9e7e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0106);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x61
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xdeb3d896);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0131);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x6c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 8
    * Segment Id for this node is: 26
    * Starting at 0x131
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0084);
      var s3 := Push2(s2, 0x013f);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0447);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s7, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 66
    * Starting at 0x447
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x447 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x13f

    requires s0.stack[3] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13f;
      assert s1.Peek(3) == 0x84;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0459);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s10, gas - 1)
      else
        ExecuteFromCFGNode_s10(s10, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 67
    * Starting at 0x455
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x455 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x13f

    requires s0.stack[4] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x13f;
      assert s1.Peek(5) == 0x84;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 11
    * Segment Id for this node is: 68
    * Starting at 0x459
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x459 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x13f

    requires s0.stack[4] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13f;
      assert s1.Peek(4) == 0x84;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s7, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 27
    * Starting at 0x13f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x84;
      var s2 := SLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s4, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 10
    * Starting at 0x84
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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
      ExecuteFromCFGNode_s14(s8, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 11
    * Starting at 0x8e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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

  /** Node 15
    * Segment Id for this node is: 23
    * Starting at 0x106
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0119);
      var s3 := Push2(s2, 0x0114);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0425);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s7, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 63
    * Starting at 0x425
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x425 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x114

    requires s0.stack[3] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x114;
      assert s1.Peek(3) == 0x119;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0438);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s11, gas - 1)
      else
        ExecuteFromCFGNode_s17(s11, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 64
    * Starting at 0x434
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x114

    requires s0.stack[5] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x114;
      assert s1.Peek(6) == 0x119;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 18
    * Segment Id for this node is: 65
    * Starting at 0x438
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x438 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x114

    requires s0.stack[5] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x114;
      assert s1.Peek(5) == 0x119;
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
      assert s11.Peek(1) == 0x114;
      assert s11.Peek(4) == 0x119;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s14, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 24
    * Starting at 0x114
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x119;
      var s2 := Push2(s1, 0x0375);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s3, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 49
    * Starting at 0x375
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x375 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x119;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Add(s4);
      var s6 := Dup3(s5);
      var s7 := Dup2(s6);
      var s8 := SLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Lt(s9);
      var s11 := Push2(s10, 0x038c);
      assert s11.Peek(0) == 0x38c;
      assert s11.Peek(7) == 0x119;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s12, gas - 1)
      else
        ExecuteFromCFGNode_s21(s12, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 50
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x038c);
      assert s1.Peek(0) == 0x38c;
      assert s1.Peek(6) == 0x119;
      var s2 := Push2(s1, 0x0481);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 71
    * Starting at 0x481
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x481 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x38c

    requires s0.stack[6] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x38c;
      assert s1.Peek(6) == 0x119;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x38c;
      assert s11.Peek(8) == 0x119;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 23
    * Segment Id for this node is: 51
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x119;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := SLoad(s10);
      assert s11.Peek(4) == 0x119;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Swap4(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x119;
      var s22 := Pop(s21);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s23, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 25
    * Starting at 0x119
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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
      var s16 := Push2(s15, 0x008e);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s17, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 19
    * Starting at 0xe6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x00f2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s6, gas - 1)
      else
        ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 20
    * Starting at 0xee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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

  /** Node 27
    * Segment Id for this node is: 21
    * Starting at 0xf2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00b7);
      var s4 := Push2(s3, 0x0101);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x03f0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s8, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 59
    * Starting at 0x3f0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x101

    requires s0.stack[3] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x101;
      assert s1.Peek(3) == 0xb7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0405);
      assert s11.Peek(0) == 0x405;
      assert s11.Peek(7) == 0x101;
      assert s11.Peek(8) == 0xb7;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s12, gas - 1)
      else
        ExecuteFromCFGNode_s29(s12, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 60
    * Starting at 0x401
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x401 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x101

    requires s0.stack[6] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x101;
      assert s1.Peek(7) == 0xb7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 30
    * Segment Id for this node is: 61
    * Starting at 0x405
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x101

    requires s0.stack[6] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x101;
      assert s1.Peek(6) == 0xb7;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0415);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03a8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s11, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 52
    * Starting at 0x3a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x415

    requires s0.stack[7] == 0x101

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x415;
      assert s1.Peek(7) == 0x101;
      assert s1.Peek(8) == 0xb7;
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
      assert s11.Peek(4) == 0x415;
      assert s11.Peek(10) == 0x101;
      assert s11.Peek(11) == 0xb7;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x03bf);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s14, gas - 1)
      else
        ExecuteFromCFGNode_s32(s14, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 53
    * Starting at 0x3bb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x415

    requires s0.stack[8] == 0x101

    requires s0.stack[9] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x415;
      assert s1.Peek(9) == 0x101;
      assert s1.Peek(10) == 0xb7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 54
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x415

    requires s0.stack[8] == 0x101

    requires s0.stack[9] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x415;
      assert s1.Peek(8) == 0x101;
      assert s1.Peek(9) == 0xb7;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 62
    * Starting at 0x415
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x101

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x101;
      assert s1.Peek(7) == 0xb7;
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
      assert s11.Peek(4) == 0x101;
      assert s11.Peek(5) == 0xb7;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s15, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 22
    * Starting at 0x101
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb7;
      var s2 := Push2(s1, 0x02cc);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 44
    * Starting at 0x2cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xb7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Dup5(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(4) == 0xb7;
      var s22 := Push1(s21, 0xff);
      var s23 := And(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0311);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s26, gas - 1)
      else
        ExecuteFromCFGNode_s37(s26, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 45
    * Starting at 0x2f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(4) == 0xb7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup3(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0xb7;
      var s12 := Push1(s11, 0x01);
      var s13 := Dup5(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0xb7;
      var s22 := SStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s26, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 16
    * Starting at 0xb7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Stop(s1);
      // Segment is terminal (Revert, Stop or Return)
      s2
  }

  /** Node 39
    * Segment Id for this node is: 46
    * Starting at 0x311
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x311 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0xb7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Dup6(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Dup1(s20);
      assert s21.Peek(8) == 0xb7;
      var s22 := Dup4(s21);
      var s23 := Keccak256(s22);
      var s24 := Dup1(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := Not(s26);
      var s28 := And(s27);
      var s29 := Push1(s28, 0x01);
      var s30 := Swap1(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(11) == 0xb7;
      var s32 := Or(s31);
      var s33 := Swap1(s32);
      var s34 := Swap2(s33);
      var s35 := SStore(s34);
      var s36 := Dup8(s35);
      var s37 := Dup2(s36);
      var s38 := Add(s37);
      var s39 := Dup4(s38);
      var s40 := MStore(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s41, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 47
    * Starting at 0x343
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x343 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      assert s1.Peek(10) == 0xb7;
      var s2 := Keccak256(s1);
      var s3 := Dup7(s2);
      var s4 := Swap1(s3);
      var s5 := SStore(s4);
      var s6 := Dup8(s5);
      var s7 := SLoad(s6);
      var s8 := Push1(s7, 0x02);
      var s9 := Dup10(s8);
      var s10 := Add(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(11) == 0xb7;
      var s12 := MStore(s11);
      var s13 := Swap2(s12);
      var s14 := Dup5(s13);
      var s15 := Keccak256(s14);
      var s16 := Dup3(s15);
      var s17 := Swap1(s16);
      var s18 := SStore(s17);
      var s19 := Dup2(s18);
      var s20 := Add(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(9) == 0xb7;
      var s22 := SStore(s21);
      var s23 := Dup7(s22);
      var s24 := Dup4(s23);
      var s25 := MStore(s24);
      var s26 := Swap2(s25);
      var s27 := Keccak256(s26);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push1(s30, 0x01);
      assert s31.Peek(7) == 0xb7;
      var s32 := Push1(s31, 0x01);
      var s33 := Push1(s32, 0xa0);
      var s34 := Shl(s33);
      var s35 := Sub(s34);
      var s36 := Not(s35);
      var s37 := And(s36);
      var s38 := Swap1(s37);
      var s39 := Swap2(s38);
      var s40 := Or(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s41(s41, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 48
    * Starting at 0x370
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x370 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := SStore(s0);
      assert s1.Peek(3) == 0xb7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s5, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 17
    * Starting at 0xb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0084);
      var s3 := Push2(s2, 0x00c7);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x03c4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s7, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 55
    * Starting at 0x3c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0xc7

    requires s0.stack[3] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc7;
      assert s1.Peek(3) == 0x84;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x03d7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s11, gas - 1)
      else
        ExecuteFromCFGNode_s44(s11, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 56
    * Starting at 0x3d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0xc7

    requires s0.stack[5] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xc7;
      assert s1.Peek(6) == 0x84;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 45
    * Segment Id for this node is: 57
    * Starting at 0x3d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0xc7

    requires s0.stack[5] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc7;
      assert s1.Peek(5) == 0x84;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x03e7);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03a8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s11, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 52
    * Starting at 0x3a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x3e7

    requires s0.stack[6] == 0xc7

    requires s0.stack[7] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e7;
      assert s1.Peek(6) == 0xc7;
      assert s1.Peek(7) == 0x84;
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
      assert s11.Peek(4) == 0x3e7;
      assert s11.Peek(9) == 0xc7;
      assert s11.Peek(10) == 0x84;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x03bf);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s14, gas - 1)
      else
        ExecuteFromCFGNode_s47(s14, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 53
    * Starting at 0x3bb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x3e7

    requires s0.stack[7] == 0xc7

    requires s0.stack[8] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x3e7;
      assert s1.Peek(8) == 0xc7;
      assert s1.Peek(9) == 0x84;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 48
    * Segment Id for this node is: 54
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x3e7

    requires s0.stack[7] == 0xc7

    requires s0.stack[8] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e7;
      assert s1.Peek(7) == 0xc7;
      assert s1.Peek(8) == 0x84;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s5, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 58
    * Starting at 0x3e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0xc7

    requires s0.stack[6] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc7;
      assert s1.Peek(6) == 0x84;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s9, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 18
    * Starting at 0xc7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x84;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(2) == 0x84;
      var s12 := Push1(s11, 0x01);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(1) == 0x84;
      var s22 := SLoad(s21);
      var s23 := Swap1(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s24, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 12
    * Starting at 0x97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x00a3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s6, gas - 1)
      else
        ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 13
    * Starting at 0x9f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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

  /** Node 53
    * Segment Id for this node is: 14
    * Starting at 0xa3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00b7);
      var s4 := Push2(s3, 0x00b2);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x03c4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s8, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 55
    * Starting at 0x3c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0xb2

    requires s0.stack[3] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb2;
      assert s1.Peek(3) == 0xb7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x03d7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s11, gas - 1)
      else
        ExecuteFromCFGNode_s55(s11, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 56
    * Starting at 0x3d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0xb2

    requires s0.stack[5] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xb2;
      assert s1.Peek(6) == 0xb7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 56
    * Segment Id for this node is: 57
    * Starting at 0x3d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0xb2

    requires s0.stack[5] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb2;
      assert s1.Peek(5) == 0xb7;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x03e7);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03a8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s11, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 52
    * Starting at 0x3a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x3e7

    requires s0.stack[6] == 0xb2

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e7;
      assert s1.Peek(6) == 0xb2;
      assert s1.Peek(7) == 0xb7;
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
      assert s11.Peek(4) == 0x3e7;
      assert s11.Peek(9) == 0xb2;
      assert s11.Peek(10) == 0xb7;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x03bf);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s14, gas - 1)
      else
        ExecuteFromCFGNode_s58(s14, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 53
    * Starting at 0x3bb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x3e7

    requires s0.stack[7] == 0xb2

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x3e7;
      assert s1.Peek(8) == 0xb2;
      assert s1.Peek(9) == 0xb7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 59
    * Segment Id for this node is: 54
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x3e7

    requires s0.stack[7] == 0xb2

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e7;
      assert s1.Peek(7) == 0xb2;
      assert s1.Peek(8) == 0xb7;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 58
    * Starting at 0x3e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0xb2

    requires s0.stack[6] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb2;
      assert s1.Peek(6) == 0xb7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s9, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 15
    * Starting at 0xb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb7;
      var s2 := Push2(s1, 0x0191);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s3, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 32
    * Starting at 0x191
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0xb7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap1(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(3) == 0xb7;
      var s22 := Push1(s21, 0xff);
      var s23 := And(s22);
      var s24 := Push2(s23, 0x01b7);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s25, gas - 1)
      else
        ExecuteFromCFGNode_s63(s25, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 33
    * Starting at 0x1b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0xb7;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s3, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 34
    * Starting at 0x1b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb7;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0xb7;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Dup1(s20);
      assert s21.Peek(6) == 0xb7;
      var s22 := Dup4(s21);
      var s23 := Keccak256(s22);
      var s24 := Dup1(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := Not(s26);
      var s28 := And(s27);
      var s29 := Swap1(s28);
      var s30 := SStore(s29);
      var s31 := Push1(s30, 0x01);
      assert s31.Peek(6) == 0xb7;
      var s32 := Dup1(s31);
      var s33 := Dup7(s32);
      var s34 := Add(s33);
      var s35 := Dup4(s34);
      var s36 := MStore(s35);
      var s37 := Dup2(s36);
      var s38 := Dup5(s37);
      var s39 := Keccak256(s38);
      var s40 := Dup5(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s41, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 35
    * Starting at 0x1e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := SStore(s0);
      assert s1.Peek(6) == 0xb7;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Swap3(s5);
      var s7 := MStore(s6);
      var s8 := Dup3(s7);
      var s9 := Keccak256(s8);
      var s10 := SLoad(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xb7;
      var s12 := SLoad(s11);
      var s13 := Swap1(s12);
      var s14 := Swap3(s13);
      var s15 := Swap2(s14);
      var s16 := Push2(s15, 0x0201);
      var s17 := Swap2(s16);
      var s18 := Push2(s17, 0x0460);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s19, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 69
    * Starting at 0x460
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x201

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x201;
      assert s1.Peek(7) == 0xb7;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x018b);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s10, gas - 1)
      else
        ExecuteFromCFGNode_s67(s10, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 70
    * Starting at 0x46c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x201

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x201;
      assert s1.Peek(9) == 0xb7;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 68
    * Segment Id for this node is: 31
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x201

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x201;
      assert s1.Peek(8) == 0xb7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s6, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 36
    * Starting at 0x201
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x201 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Add(s6);
      var s8 := Dup3(s7);
      var s9 := Dup2(s8);
      var s10 := SLoad(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(9) == 0xb7;
      var s12 := Lt(s11);
      var s13 := Push2(s12, 0x021a);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s14, gas - 1)
      else
        ExecuteFromCFGNode_s70(s14, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 37
    * Starting at 0x213
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x021a);
      assert s1.Peek(0) == 0x21a;
      assert s1.Peek(8) == 0xb7;
      var s2 := Push2(s1, 0x0481);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s3, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 71
    * Starting at 0x481
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x481 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x21a

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x21a;
      assert s1.Peek(8) == 0xb7;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x21a;
      assert s11.Peek(10) == 0xb7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 72
    * Segment Id for this node is: 38
    * Starting at 0x21a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xb7;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := Keccak256(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0xb7;
      var s12 := Add(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := And(s20);
      assert s21.Peek(9) == 0xb7;
      var s22 := Dup1(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x02);
      var s26 := Dup10(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x40);
      assert s31.Peek(9) == 0xb7;
      var s32 := Dup1(s31);
      var s33 := Dup5(s32);
      var s34 := Keccak256(s33);
      var s35 := Dup8(s34);
      var s36 := Swap1(s35);
      var s37 := SStore(s36);
      var s38 := Swap1(s37);
      var s39 := Dup8(s38);
      var s40 := And(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s41, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 39
    * Starting at 0x24a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(8) == 0xb7;
      var s2 := Dup3(s1);
      var s3 := Keccak256(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Swap2(s5);
      var s7 := SStore(s6);
      var s8 := Dup6(s7);
      var s9 := SLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(7) == 0xb7;
      var s12 := Pop(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := Dup7(s14);
      var s16 := Swap1(s15);
      var s17 := Dup6(s16);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := Lt(s19);
      var s21 := Push2(s20, 0x0269);
      assert s21.Peek(0) == 0x269;
      assert s21.Peek(10) == 0xb7;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s22, gas - 1)
      else
        ExecuteFromCFGNode_s74(s22, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 40
    * Starting at 0x262
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x262 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0269);
      assert s1.Peek(0) == 0x269;
      assert s1.Peek(9) == 0xb7;
      var s2 := Push2(s1, 0x0481);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s3, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 71
    * Starting at 0x481
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x481 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x269

    requires s0.stack[9] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x269;
      assert s1.Peek(9) == 0xb7;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x269;
      assert s11.Peek(11) == 0xb7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 76
    * Segment Id for this node is: 41
    * Starting at 0x269
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0xb7;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Keccak256(s8);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(8) == 0xb7;
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := And(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(10) == 0xb7;
      var s22 := Push1(s21, 0xa0);
      var s23 := Shl(s22);
      var s24 := Sub(s23);
      var s25 := Swap3(s24);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := And(s27);
      var s29 := Swap2(s28);
      var s30 := Swap1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(8) == 0xb7;
      var s32 := Or(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Dup5(s34);
      var s36 := SLoad(s35);
      var s37 := Dup6(s36);
      var s38 := Swap1(s37);
      var s39 := Dup1(s38);
      var s40 := Push2(s39, 0x02a3);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s41, gas - 1)
      else
        ExecuteFromCFGNode_s77(s41, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 42
    * Starting at 0x29c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02a3);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(8) == 0xb7;
      var s2 := Push2(s1, 0x0497);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s3, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 72
    * Starting at 0x497
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x2a3

    requires s0.stack[8] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(8) == 0xb7;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x31);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2a3;
      assert s11.Peek(10) == 0xb7;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 79
    * Segment Id for this node is: 43
    * Starting at 0x2a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0xb7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xb7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap1(s6);
      var s8 := Keccak256(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(9) == 0xb7;
      var s12 := Not(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Dup1(s15);
      var s17 := SLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(12) == 0xb7;
      var s22 := Sub(s21);
      var s23 := Not(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := SStore(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(3) == 0xb7;
      var s32 := Pop(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s35, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 8
    * Starting at 0x71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0084);
      var s3 := Push2(s2, 0x007f);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x03c4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s7, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 55
    * Starting at 0x3c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x7f

    requires s0.stack[3] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7f;
      assert s1.Peek(3) == 0x84;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x03d7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s11, gas - 1)
      else
        ExecuteFromCFGNode_s82(s11, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 56
    * Starting at 0x3d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x7f

    requires s0.stack[5] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x7f;
      assert s1.Peek(6) == 0x84;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 83
    * Segment Id for this node is: 57
    * Starting at 0x3d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x7f

    requires s0.stack[5] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7f;
      assert s1.Peek(5) == 0x84;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x03e7);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03a8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s11, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 52
    * Starting at 0x3a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x3e7

    requires s0.stack[6] == 0x7f

    requires s0.stack[7] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e7;
      assert s1.Peek(6) == 0x7f;
      assert s1.Peek(7) == 0x84;
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
      assert s11.Peek(4) == 0x3e7;
      assert s11.Peek(9) == 0x7f;
      assert s11.Peek(10) == 0x84;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x03bf);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s14, gas - 1)
      else
        ExecuteFromCFGNode_s85(s14, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 53
    * Starting at 0x3bb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x3e7

    requires s0.stack[7] == 0x7f

    requires s0.stack[8] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x3e7;
      assert s1.Peek(8) == 0x7f;
      assert s1.Peek(9) == 0x84;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 86
    * Segment Id for this node is: 54
    * Starting at 0x3bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x3e7

    requires s0.stack[7] == 0x7f

    requires s0.stack[8] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e7;
      assert s1.Peek(7) == 0x7f;
      assert s1.Peek(8) == 0x84;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 58
    * Starting at 0x3e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x7f

    requires s0.stack[6] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7f;
      assert s1.Peek(6) == 0x84;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s9, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 9
    * Starting at 0x7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x84;
      var s2 := Push2(s1, 0x0143);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s3, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 28
    * Starting at 0x143
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x84;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x84;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup2(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(4) == 0x84;
      var s22 := Push1(s21, 0xff);
      var s23 := And(s22);
      var s24 := Push2(s23, 0x016e);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s25, gas - 1)
      else
        ExecuteFromCFGNode_s90(s25, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 29
    * Starting at 0x166
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x166 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x84;
      var s2 := Push1(s1, 0x00);
      var s3 := Not(s2);
      var s4 := Push2(s3, 0x018b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s5, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 31
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x84;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s6, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 30
    * Starting at 0x16e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x84

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x84;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x84;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x02);
      var s15 := Dup4(s14);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(3) == 0x84;
      var s22 := SLoad(s21);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s91(s22, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 7
    * Starting at 0x6c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c as nat
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
}
