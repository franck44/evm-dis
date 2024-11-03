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
      var s6 := Push2(s5, 0x0036);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s7, gas - 1)
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
      var s6 := Push4(s5, 0x41ebf682);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x003b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s9, gas - 1)
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
      var s2 := Push4(s1, 0x5578110c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0057);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s6(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x36
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 6
    * Segment Id for this node is: 9
    * Starting at 0x57
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x005f);
      var s3 := Push2(s2, 0x017c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s4, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 18
    * Starting at 0x17c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Swap1(s7);
      var s9 := Div(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(1) == 0x5f;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s13, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 10
    * Starting at 0x5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5f;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x006c);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x039a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s8, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 56
    * Starting at 0x39a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x6c

    requires s0.stack[3] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6c;
      assert s1.Peek(3) == 0x5f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x03af);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x3af;
      assert s11.Peek(5) == 0x6c;
      assert s11.Peek(6) == 0x5f;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x02a9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s14, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 42
    * Starting at 0x2a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x3af

    requires s0.stack[6] == 0x6c

    requires s0.stack[7] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3af;
      assert s1.Peek(6) == 0x6c;
      assert s1.Peek(7) == 0x5f;
      var s2 := Push2(s1, 0x02b2);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x03fc);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 63
    * Starting at 0x3fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x2b2

    requires s0.stack[4] == 0x3af

    requires s0.stack[8] == 0x6c

    requires s0.stack[9] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2b2;
      assert s1.Peek(4) == 0x3af;
      assert s1.Peek(8) == 0x6c;
      assert s1.Peek(9) == 0x5f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0407);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x040e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s6, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 65
    * Starting at 0x40e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x407

    requires s0.stack[4] == 0x2b2

    requires s0.stack[7] == 0x3af

    requires s0.stack[11] == 0x6c

    requires s0.stack[12] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x407;
      assert s1.Peek(4) == 0x2b2;
      assert s1.Peek(7) == 0x3af;
      assert s1.Peek(11) == 0x6c;
      assert s1.Peek(12) == 0x5f;
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
      ExecuteFromCFGNode_s13(s11, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 64
    * Starting at 0x407
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x407 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x2b2

    requires s0.stack[6] == 0x3af

    requires s0.stack[10] == 0x6c

    requires s0.stack[11] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2b2;
      assert s1.Peek(6) == 0x3af;
      assert s1.Peek(10) == 0x6c;
      assert s1.Peek(11) == 0x5f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s7, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 43
    * Starting at 0x2b2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3af

    requires s0.stack[7] == 0x6c

    requires s0.stack[8] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3af;
      assert s1.Peek(7) == 0x6c;
      assert s1.Peek(8) == 0x5f;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s6, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 57
    * Starting at 0x3af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x6c

    requires s0.stack[4] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6c;
      assert s1.Peek(4) == 0x5f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s6, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 11
    * Starting at 0x6c
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5f;
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

  /** Node 17
    * Segment Id for this node is: 6
    * Starting at 0x3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0055);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0050);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x50;
      assert s11.Peek(3) == 0x55;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0234);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s14, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 33
    * Starting at 0x234
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x234 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x50

    requires s0.stack[3] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x50;
      assert s1.Peek(3) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Dup6(s6);
      var s8 := Dup8(s7);
      var s9 := Sub(s8);
      var s10 := SLt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(7) == 0x50;
      assert s11.Peek(8) == 0x55;
      var s12 := Push2(s11, 0x024a);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s13, gas - 1)
      else
        ExecuteFromCFGNode_s19(s13, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 34
    * Starting at 0x246
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x246 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x50

    requires s0.stack[7] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x50;
      assert s1.Peek(8) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 20
    * Segment Id for this node is: 35
    * Starting at 0x24a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x50

    requires s0.stack[7] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x50;
      assert s1.Peek(7) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0264);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s11, gas - 1)
      else
        ExecuteFromCFGNode_s21(s11, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 36
    * Starting at 0x260
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x50

    requires s0.stack[8] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x50;
      assert s1.Peek(9) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 37
    * Starting at 0x264
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x264 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x50

    requires s0.stack[8] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x50;
      assert s1.Peek(8) == 0x55;
      var s2 := Push2(s1, 0x0270);
      var s3 := Dup8(s2);
      var s4 := Dup3(s3);
      var s5 := Dup9(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x01ea);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s8, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 26
    * Starting at 0x1ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x270

    requires s0.stack[10] == 0x50

    requires s0.stack[11] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x270;
      assert s1.Peek(10) == 0x50;
      assert s1.Peek(11) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x01fc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s10, gas - 1)
      else
        ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 27
    * Starting at 0x1f8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x270

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x270;
      assert s1.Peek(13) == 0x50;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 28
    * Starting at 0x1fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x270

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x270;
      assert s1.Peek(12) == 0x50;
      assert s1.Peek(13) == 0x55;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0215);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s11, gas - 1)
      else
        ExecuteFromCFGNode_s26(s11, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 29
    * Starting at 0x211
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x211 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x270

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x270;
      assert s1.Peek(13) == 0x50;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 27
    * Segment Id for this node is: 30
    * Starting at 0x215
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x215 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x270

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x270;
      assert s1.Peek(12) == 0x50;
      assert s1.Peek(13) == 0x55;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := Mul(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x270;
      assert s11.Peek(15) == 0x50;
      assert s11.Peek(16) == 0x55;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x022d);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s16, gas - 1)
      else
        ExecuteFromCFGNode_s28(s16, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 31
    * Starting at 0x229
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x270

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x270;
      assert s1.Peek(13) == 0x50;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 29
    * Segment Id for this node is: 32
    * Starting at 0x22d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x270

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x270;
      assert s1.Peek(12) == 0x50;
      assert s1.Peek(13) == 0x55;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s7, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 38
    * Starting at 0x270
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x270 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x50

    requires s0.stack[10] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x50;
      assert s1.Peek(10) == 0x55;
      var s2 := Swap5(s1);
      var s3 := Pop(s2);
      var s4 := Swap5(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Push8(s10, 0xffffffffffffffff);
      assert s11.Peek(8) == 0x50;
      assert s11.Peek(9) == 0x55;
      var s12 := Dup2(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x028f);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s16, gas - 1)
      else
        ExecuteFromCFGNode_s31(s16, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 39
    * Starting at 0x28b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x50

    requires s0.stack[8] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x50;
      assert s1.Peek(9) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 32
    * Segment Id for this node is: 40
    * Starting at 0x28f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x50

    requires s0.stack[8] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x50;
      assert s1.Peek(8) == 0x55;
      var s2 := Push2(s1, 0x029b);
      var s3 := Dup8(s2);
      var s4 := Dup3(s3);
      var s5 := Dup9(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x01a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s8, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 19
    * Starting at 0x1a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x29b

    requires s0.stack[10] == 0x50

    requires s0.stack[11] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x29b;
      assert s1.Peek(10) == 0x50;
      assert s1.Peek(11) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := Push2(s8, 0x01b2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s10, gas - 1)
      else
        ExecuteFromCFGNode_s34(s10, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 20
    * Starting at 0x1ae
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x29b

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x29b;
      assert s1.Peek(13) == 0x50;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 35
    * Segment Id for this node is: 21
    * Starting at 0x1b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x29b

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x29b;
      assert s1.Peek(12) == 0x50;
      assert s1.Peek(13) == 0x55;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x01cb);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s11, gas - 1)
      else
        ExecuteFromCFGNode_s36(s11, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 22
    * Starting at 0x1c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x29b

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x29b;
      assert s1.Peek(13) == 0x50;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 37
    * Segment Id for this node is: 23
    * Starting at 0x1cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x29b

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x29b;
      assert s1.Peek(12) == 0x50;
      assert s1.Peek(13) == 0x55;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := Mul(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x29b;
      assert s11.Peek(15) == 0x50;
      assert s11.Peek(16) == 0x55;
      var s12 := Add(s11);
      var s13 := Gt(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x01e3);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s16, gas - 1)
      else
        ExecuteFromCFGNode_s38(s16, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 24
    * Starting at 0x1df
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x29b

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x29b;
      assert s1.Peek(13) == 0x50;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 39
    * Segment Id for this node is: 25
    * Starting at 0x1e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x29b

    requires s0.stack[12] == 0x50

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x29b;
      assert s1.Peek(12) == 0x50;
      assert s1.Peek(13) == 0x55;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 41
    * Starting at 0x29b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x50

    requires s0.stack[10] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x50;
      assert s1.Peek(10) == 0x55;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap6(s7);
      var s9 := Swap2(s8);
      var s10 := Swap5(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x50;
      assert s11.Peek(6) == 0x55;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s14, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 7
    * Starting at 0x50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x55;
      var s2 := Push2(s1, 0x0075);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s3, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 12
    * Starting at 0x75
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Swap1(s7);
      var s9 := Div(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(5) == 0x55;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Caller(s13);
      var s15 := Push20(s14, 0xffffffffffffffffffffffffffffffffffffffff);
      var s16 := And(s15);
      var s17 := Eq(s16);
      var s18 := Push2(s17, 0x0103);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s19, gas - 1)
      else
        ExecuteFromCFGNode_s43(s19, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 13
    * Starting at 0xc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x55;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x00fa);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x03b5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s11, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 58
    * Starting at 0x3b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xfa

    requires s0.stack[6] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa;
      assert s1.Peek(6) == 0x55;
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
      assert s11.Peek(4) == 0xfa;
      assert s11.Peek(9) == 0x55;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x03ce);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0302);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s18, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 50
    * Starting at 0x302
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3ce

    requires s0.stack[4] == 0xfa

    requires s0.stack[9] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ce;
      assert s1.Peek(4) == 0xfa;
      assert s1.Peek(9) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x030f);
      var s4 := Push1(s3, 0x27);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x03e0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s7, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 61
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x30f

    requires s0.stack[5] == 0x3ce

    requires s0.stack[8] == 0xfa

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x30f;
      assert s1.Peek(5) == 0x3ce;
      assert s1.Peek(8) == 0xfa;
      assert s1.Peek(13) == 0x55;
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
      assert s11.Peek(0) == 0x30f;
      assert s11.Peek(6) == 0x3ce;
      assert s11.Peek(9) == 0xfa;
      assert s11.Peek(14) == 0x55;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s15, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 51
    * Starting at 0x30f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3ce

    requires s0.stack[6] == 0xfa

    requires s0.stack[11] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ce;
      assert s1.Peek(6) == 0xfa;
      assert s1.Peek(11) == 0x55;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x4f6e6c792046414252595820534146452063616e2063616c6c20746869732066);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x756e6374696f6e00000000000000000000000000000000000000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x3ce;
      assert s11.Peek(8) == 0xfa;
      assert s11.Peek(13) == 0x55;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x3ce;
      assert s21.Peek(4) == 0xfa;
      assert s21.Peek(9) == 0x55;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s22, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 59
    * Starting at 0x3ce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xfa

    requires s0.stack[8] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xfa;
      assert s1.Peek(8) == 0x55;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s7, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 14
    * Starting at 0xfa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x55;
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

  /** Node 50
    * Segment Id for this node is: 15
    * Starting at 0x103
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x55;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push2(s5, 0x0113);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0368);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s11, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 52
    * Starting at 0x368
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x113

    requires s0.stack[8] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x113;
      assert s1.Peek(8) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0375);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Dup7(s5);
      var s7 := Push2(s6, 0x02b8);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s8, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 44
    * Starting at 0x2b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x375

    requires s0.stack[8] == 0x113

    requires s0.stack[13] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x375;
      assert s1.Peek(8) == 0x113;
      assert s1.Peek(13) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02c4);
      var s4 := Dup4(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x03d5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s7, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 60
    * Starting at 0x3d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x2c4

    requires s0.stack[7] == 0x375

    requires s0.stack[12] == 0x113

    requires s0.stack[17] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c4;
      assert s1.Peek(7) == 0x375;
      assert s1.Peek(12) == 0x113;
      assert s1.Peek(17) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s10, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 45
    * Starting at 0x2c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x375

    requires s0.stack[10] == 0x113

    requires s0.stack[15] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x375;
      assert s1.Peek(10) == 0x113;
      assert s1.Peek(15) == 0x55;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x02d1);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x042e);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s9, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 66
    * Starting at 0x42e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x2d1

    requires s0.stack[8] == 0x375

    requires s0.stack[13] == 0x113

    requires s0.stack[18] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2d1;
      assert s1.Peek(8) == 0x375;
      assert s1.Peek(13) == 0x113;
      assert s1.Peek(18) == 0x55;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Dup4(s3);
      var s5 := CallDataCopy(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup4(s6);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x2d1;
      assert s11.Peek(7) == 0x375;
      assert s11.Peek(12) == 0x113;
      assert s11.Peek(17) == 0x55;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s14, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 46
    * Starting at 0x2d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x375

    requires s0.stack[9] == 0x113

    requires s0.stack[14] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x375;
      assert s1.Peek(9) == 0x113;
      assert s1.Peek(14) == 0x55;
      var s2 := Dup3(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap4(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x375;
      assert s11.Peek(6) == 0x113;
      assert s11.Peek(11) == 0x55;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s12, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 53
    * Starting at 0x375
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x375 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x113

    requires s0.stack[10] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x113;
      assert s1.Peek(10) == 0x55;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap4(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x113;
      assert s11.Peek(6) == 0x55;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s12, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 16
    * Starting at 0x113
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x55;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Keccak256(s7);
      var s9 := Dup5(s8);
      var s10 := Dup5(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(8) == 0x55;
      var s12 := MLoad(s11);
      var s13 := Push2(s12, 0x012b);
      var s14 := Swap3(s13);
      var s15 := Swap2(s14);
      var s16 := Swap1(s15);
      var s17 := Push2(s16, 0x0381);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s18, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 54
    * Starting at 0x381
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x381 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x12b

    requires s0.stack[9] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12b;
      assert s1.Peek(9) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x038e);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Dup7(s5);
      var s7 := Push2(s6, 0x02dd);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s8, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 47
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x38e

    requires s0.stack[8] == 0x12b

    requires s0.stack[14] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38e;
      assert s1.Peek(8) == 0x12b;
      assert s1.Peek(14) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02e9);
      var s4 := Dup4(s3);
      var s5 := Dup6(s4);
      var s6 := Push2(s5, 0x03f1);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s7, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 62
    * Starting at 0x3f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x2e9

    requires s0.stack[7] == 0x38e

    requires s0.stack[12] == 0x12b

    requires s0.stack[18] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2e9;
      assert s1.Peek(7) == 0x38e;
      assert s1.Peek(12) == 0x12b;
      assert s1.Peek(18) == 0x55;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s10, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 48
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x38e

    requires s0.stack[10] == 0x12b

    requires s0.stack[16] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x38e;
      assert s1.Peek(10) == 0x12b;
      assert s1.Peek(16) == 0x55;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x02f6);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x042e);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s9, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 66
    * Starting at 0x42e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x2f6

    requires s0.stack[8] == 0x38e

    requires s0.stack[13] == 0x12b

    requires s0.stack[19] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f6;
      assert s1.Peek(8) == 0x38e;
      assert s1.Peek(13) == 0x12b;
      assert s1.Peek(19) == 0x55;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Dup4(s3);
      var s5 := CallDataCopy(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup4(s6);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x2f6;
      assert s11.Peek(7) == 0x38e;
      assert s11.Peek(12) == 0x12b;
      assert s11.Peek(18) == 0x55;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s14, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 49
    * Starting at 0x2f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x38e

    requires s0.stack[9] == 0x12b

    requires s0.stack[15] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x38e;
      assert s1.Peek(9) == 0x12b;
      assert s1.Peek(15) == 0x55;
      var s2 := Dup3(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap4(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x38e;
      assert s11.Peek(6) == 0x12b;
      assert s11.Peek(12) == 0x55;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s12, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 55
    * Starting at 0x38e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x12b

    requires s0.stack[11] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x12b;
      assert s1.Peek(11) == 0x55;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap4(s6);
      var s8 := Swap3(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x12b;
      assert s11.Peek(7) == 0x55;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s12, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 17
    * Starting at 0x12b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x55

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x55;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Keccak256(s7);
      var s9 := Caller(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x55;
      var s12 := Push32(s11, 0xfaf5f4d4e8e968365df1d0cda79f0528802b45779d61711875dcb135174fb093);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Swap2(s17);
      var s19 := Sub(s18);
      var s20 := Swap1(s19);
      var s21 := Log4(s20);
      assert s21.Peek(4) == 0x55;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s26, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 8
    * Starting at 0x55
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55 as nat
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

  /** Node 68
    * Segment Id for this node is: 5
    * Starting at 0x36
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36 as nat
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
