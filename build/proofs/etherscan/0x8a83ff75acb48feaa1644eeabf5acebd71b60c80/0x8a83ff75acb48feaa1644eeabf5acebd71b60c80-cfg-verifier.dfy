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
      var s6 := Push2(s5, 0x009c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s7, gas - 1)
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
      var s6 := Push4(s5, 0x831658b2);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0064);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s9, gas - 1)
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
      var s2 := Push4(s1, 0x831658b2);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0136);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s5, gas - 1)
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
      var s2 := Push4(s1, 0x91ad7973);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0154);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s5, gas - 1)
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
      var s2 := Push4(s1, 0xb4ca02d4);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0172);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd1521c8d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0190);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd4e4ffa6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ae);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x009c);
      assert s1.Peek(0) == 0x9c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 15
    * Starting at 0x9c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c as nat
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

  /** Node 11
    * Segment Id for this node is: 43
    * Starting at 0x1ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01b6);
      var s3 := Push2(s2, 0x0317);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s4, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 55
    * Starting at 0x317
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x317 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b6;
      var s2 := Push1(s1, 0x03);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x1b6;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s14, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 44
    * Starting at 0x1b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01c3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x03ef);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s8, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 74
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1c3

    requires s0.stack[3] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(3) == 0x1b6;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0402);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x402;
      assert s11.Peek(5) == 0x1c3;
      assert s11.Peek(6) == 0x1b6;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x03e0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s14, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 72
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x402

    requires s0.stack[6] == 0x1c3

    requires s0.stack[7] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x402;
      assert s1.Peek(6) == 0x1c3;
      assert s1.Peek(7) == 0x1b6;
      var s2 := Push2(s1, 0x03e9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x03cf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s5, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 70
    * Starting at 0x3cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3e9

    requires s0.stack[4] == 0x402

    requires s0.stack[8] == 0x1c3

    requires s0.stack[9] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e9;
      assert s1.Peek(4) == 0x402;
      assert s1.Peek(8) == 0x1c3;
      assert s1.Peek(9) == 0x1b6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03d9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s6, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3d9

    requires s0.stack[4] == 0x3e9

    requires s0.stack[7] == 0x402

    requires s0.stack[11] == 0x1c3

    requires s0.stack[12] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d9;
      assert s1.Peek(4) == 0x3e9;
      assert s1.Peek(7) == 0x402;
      assert s1.Peek(11) == 0x1c3;
      assert s1.Peek(12) == 0x1b6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s6, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x3d9

    requires s0.stack[7] == 0x3e9

    requires s0.stack[10] == 0x402

    requires s0.stack[14] == 0x1c3

    requires s0.stack[15] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x3d9;
      assert s1.Peek(7) == 0x3e9;
      assert s1.Peek(10) == 0x402;
      assert s1.Peek(14) == 0x1c3;
      assert s1.Peek(15) == 0x1b6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s8, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x3d9

    requires s0.stack[12] == 0x3e9

    requires s0.stack[15] == 0x402

    requires s0.stack[19] == 0x1c3

    requires s0.stack[20] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x3d9;
      assert s1.Peek(12) == 0x3e9;
      assert s1.Peek(15) == 0x402;
      assert s1.Peek(19) == 0x1c3;
      assert s1.Peek(20) == 0x1b6;
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
      ExecuteFromCFGNode_s20(s11, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x1c3

    requires s0.stack[19] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x1c3;
      assert s1.Peek(19) == 0x1b6;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x1c3

    requires s0.stack[19] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x1c3;
      assert s1.Peek(19) == 0x1b6;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s9, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x1c3

    requires s0.stack[18] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x1c3;
      assert s1.Peek(18) == 0x1b6;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x1c3

    requires s0.stack[18] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x1c3;
      assert s1.Peek(18) == 0x1b6;
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
      ExecuteFromCFGNode_s24(s11, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x3d9

    requires s0.stack[9] == 0x3e9

    requires s0.stack[12] == 0x402

    requires s0.stack[16] == 0x1c3

    requires s0.stack[17] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x3d9;
      assert s1.Peek(9) == 0x3e9;
      assert s1.Peek(12) == 0x402;
      assert s1.Peek(16) == 0x1c3;
      assert s1.Peek(17) == 0x1b6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s7, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x3d9

    requires s0.stack[6] == 0x3e9

    requires s0.stack[9] == 0x402

    requires s0.stack[13] == 0x1c3

    requires s0.stack[14] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d9;
      assert s1.Peek(6) == 0x3e9;
      assert s1.Peek(9) == 0x402;
      assert s1.Peek(13) == 0x1c3;
      assert s1.Peek(14) == 0x1b6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s7, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 71
    * Starting at 0x3d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3e9

    requires s0.stack[6] == 0x402

    requires s0.stack[10] == 0x1c3

    requires s0.stack[11] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e9;
      assert s1.Peek(6) == 0x402;
      assert s1.Peek(10) == 0x1c3;
      assert s1.Peek(11) == 0x1b6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 73
    * Starting at 0x3e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x402

    requires s0.stack[7] == 0x1c3

    requires s0.stack[8] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x402;
      assert s1.Peek(7) == 0x1c3;
      assert s1.Peek(8) == 0x1b6;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s6, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 75
    * Starting at 0x402
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1c3

    requires s0.stack[4] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c3;
      assert s1.Peek(4) == 0x1b6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s6, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 45
    * Starting at 0x1c3
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b6;
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
    * Segment Id for this node is: 40
    * Starting at 0x190
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x190 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0198);
      var s3 := Push2(s2, 0x02f2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s4, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 54
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x198;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x198;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s14, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 41
    * Starting at 0x198
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x198;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01a5);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x03ef);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s8, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 74
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1a5

    requires s0.stack[3] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1a5;
      assert s1.Peek(3) == 0x198;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0402);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x402;
      assert s11.Peek(5) == 0x1a5;
      assert s11.Peek(6) == 0x198;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x03e0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s14, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 72
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x402

    requires s0.stack[6] == 0x1a5

    requires s0.stack[7] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x402;
      assert s1.Peek(6) == 0x1a5;
      assert s1.Peek(7) == 0x198;
      var s2 := Push2(s1, 0x03e9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x03cf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s5, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 70
    * Starting at 0x3cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3e9

    requires s0.stack[4] == 0x402

    requires s0.stack[8] == 0x1a5

    requires s0.stack[9] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e9;
      assert s1.Peek(4) == 0x402;
      assert s1.Peek(8) == 0x1a5;
      assert s1.Peek(9) == 0x198;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03d9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s6, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3d9

    requires s0.stack[4] == 0x3e9

    requires s0.stack[7] == 0x402

    requires s0.stack[11] == 0x1a5

    requires s0.stack[12] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d9;
      assert s1.Peek(4) == 0x3e9;
      assert s1.Peek(7) == 0x402;
      assert s1.Peek(11) == 0x1a5;
      assert s1.Peek(12) == 0x198;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s6, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x3d9

    requires s0.stack[7] == 0x3e9

    requires s0.stack[10] == 0x402

    requires s0.stack[14] == 0x1a5

    requires s0.stack[15] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x3d9;
      assert s1.Peek(7) == 0x3e9;
      assert s1.Peek(10) == 0x402;
      assert s1.Peek(14) == 0x1a5;
      assert s1.Peek(15) == 0x198;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s8, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x3d9

    requires s0.stack[12] == 0x3e9

    requires s0.stack[15] == 0x402

    requires s0.stack[19] == 0x1a5

    requires s0.stack[20] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x3d9;
      assert s1.Peek(12) == 0x3e9;
      assert s1.Peek(15) == 0x402;
      assert s1.Peek(19) == 0x1a5;
      assert s1.Peek(20) == 0x198;
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
      ExecuteFromCFGNode_s39(s11, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x1a5

    requires s0.stack[19] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x1a5;
      assert s1.Peek(19) == 0x198;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s3, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x1a5

    requires s0.stack[19] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x1a5;
      assert s1.Peek(19) == 0x198;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s9, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x1a5

    requires s0.stack[18] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x1a5;
      assert s1.Peek(18) == 0x198;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s3, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x1a5

    requires s0.stack[18] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x1a5;
      assert s1.Peek(18) == 0x198;
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
      ExecuteFromCFGNode_s43(s11, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x3d9

    requires s0.stack[9] == 0x3e9

    requires s0.stack[12] == 0x402

    requires s0.stack[16] == 0x1a5

    requires s0.stack[17] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x3d9;
      assert s1.Peek(9) == 0x3e9;
      assert s1.Peek(12) == 0x402;
      assert s1.Peek(16) == 0x1a5;
      assert s1.Peek(17) == 0x198;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x3d9

    requires s0.stack[6] == 0x3e9

    requires s0.stack[9] == 0x402

    requires s0.stack[13] == 0x1a5

    requires s0.stack[14] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d9;
      assert s1.Peek(6) == 0x3e9;
      assert s1.Peek(9) == 0x402;
      assert s1.Peek(13) == 0x1a5;
      assert s1.Peek(14) == 0x198;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s7, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 71
    * Starting at 0x3d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3e9

    requires s0.stack[6] == 0x402

    requires s0.stack[10] == 0x1a5

    requires s0.stack[11] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e9;
      assert s1.Peek(6) == 0x402;
      assert s1.Peek(10) == 0x1a5;
      assert s1.Peek(11) == 0x198;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s7, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 73
    * Starting at 0x3e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x402

    requires s0.stack[7] == 0x1a5

    requires s0.stack[8] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x402;
      assert s1.Peek(7) == 0x1a5;
      assert s1.Peek(8) == 0x198;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s6, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 75
    * Starting at 0x402
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1a5

    requires s0.stack[4] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1a5;
      assert s1.Peek(4) == 0x198;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 42
    * Starting at 0x1a5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x198

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x198;
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

  /** Node 49
    * Segment Id for this node is: 37
    * Starting at 0x172
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x172 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x017a);
      var s3 := Push2(s2, 0x02cd);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s4, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 53
    * Starting at 0x2cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x17a;
      var s2 := Push1(s1, 0x06);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x17a;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s14, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 38
    * Starting at 0x17a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0187);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x04d3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s8, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 98
    * Starting at 0x4d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x187

    requires s0.stack[3] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x187;
      assert s1.Peek(3) == 0x17a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x04e6);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x4e6;
      assert s11.Peek(5) == 0x187;
      assert s11.Peek(6) == 0x17a;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x04c4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s14, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 96
    * Starting at 0x4c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x4e6

    requires s0.stack[6] == 0x187

    requires s0.stack[7] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4e6;
      assert s1.Peek(6) == 0x187;
      assert s1.Peek(7) == 0x17a;
      var s2 := Push2(s1, 0x04cd);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x04b3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s5, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 94
    * Starting at 0x4b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4cd

    requires s0.stack[4] == 0x4e6

    requires s0.stack[8] == 0x187

    requires s0.stack[9] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4cd;
      assert s1.Peek(4) == 0x4e6;
      assert s1.Peek(8) == 0x187;
      assert s1.Peek(9) == 0x17a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04bd);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x4bd

    requires s0.stack[4] == 0x4cd

    requires s0.stack[7] == 0x4e6

    requires s0.stack[11] == 0x187

    requires s0.stack[12] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4bd;
      assert s1.Peek(4) == 0x4cd;
      assert s1.Peek(7) == 0x4e6;
      assert s1.Peek(11) == 0x187;
      assert s1.Peek(12) == 0x17a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s6, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x4bd

    requires s0.stack[7] == 0x4cd

    requires s0.stack[10] == 0x4e6

    requires s0.stack[14] == 0x187

    requires s0.stack[15] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x4bd;
      assert s1.Peek(7) == 0x4cd;
      assert s1.Peek(10) == 0x4e6;
      assert s1.Peek(14) == 0x187;
      assert s1.Peek(15) == 0x17a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s8, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x4bd

    requires s0.stack[12] == 0x4cd

    requires s0.stack[15] == 0x4e6

    requires s0.stack[19] == 0x187

    requires s0.stack[20] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x4bd;
      assert s1.Peek(12) == 0x4cd;
      assert s1.Peek(15) == 0x4e6;
      assert s1.Peek(19) == 0x187;
      assert s1.Peek(20) == 0x17a;
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
      ExecuteFromCFGNode_s58(s11, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x4bd

    requires s0.stack[11] == 0x4cd

    requires s0.stack[14] == 0x4e6

    requires s0.stack[18] == 0x187

    requires s0.stack[19] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x4bd;
      assert s1.Peek(11) == 0x4cd;
      assert s1.Peek(14) == 0x4e6;
      assert s1.Peek(18) == 0x187;
      assert s1.Peek(19) == 0x17a;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s3, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x4bd

    requires s0.stack[11] == 0x4cd

    requires s0.stack[14] == 0x4e6

    requires s0.stack[18] == 0x187

    requires s0.stack[19] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x4bd;
      assert s1.Peek(11) == 0x4cd;
      assert s1.Peek(14) == 0x4e6;
      assert s1.Peek(18) == 0x187;
      assert s1.Peek(19) == 0x17a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s9, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x4bd

    requires s0.stack[10] == 0x4cd

    requires s0.stack[13] == 0x4e6

    requires s0.stack[17] == 0x187

    requires s0.stack[18] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x4bd;
      assert s1.Peek(10) == 0x4cd;
      assert s1.Peek(13) == 0x4e6;
      assert s1.Peek(17) == 0x187;
      assert s1.Peek(18) == 0x17a;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s3, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x4bd

    requires s0.stack[10] == 0x4cd

    requires s0.stack[13] == 0x4e6

    requires s0.stack[17] == 0x187

    requires s0.stack[18] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x4bd;
      assert s1.Peek(10) == 0x4cd;
      assert s1.Peek(13) == 0x4e6;
      assert s1.Peek(17) == 0x187;
      assert s1.Peek(18) == 0x17a;
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
      ExecuteFromCFGNode_s62(s11, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x4bd

    requires s0.stack[9] == 0x4cd

    requires s0.stack[12] == 0x4e6

    requires s0.stack[16] == 0x187

    requires s0.stack[17] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x4bd;
      assert s1.Peek(9) == 0x4cd;
      assert s1.Peek(12) == 0x4e6;
      assert s1.Peek(16) == 0x187;
      assert s1.Peek(17) == 0x17a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s7, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x4bd

    requires s0.stack[6] == 0x4cd

    requires s0.stack[9] == 0x4e6

    requires s0.stack[13] == 0x187

    requires s0.stack[14] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4bd;
      assert s1.Peek(6) == 0x4cd;
      assert s1.Peek(9) == 0x4e6;
      assert s1.Peek(13) == 0x187;
      assert s1.Peek(14) == 0x17a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s7, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 95
    * Starting at 0x4bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x4cd

    requires s0.stack[6] == 0x4e6

    requires s0.stack[10] == 0x187

    requires s0.stack[11] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4cd;
      assert s1.Peek(6) == 0x4e6;
      assert s1.Peek(10) == 0x187;
      assert s1.Peek(11) == 0x17a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s7, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 97
    * Starting at 0x4cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4e6

    requires s0.stack[7] == 0x187

    requires s0.stack[8] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4e6;
      assert s1.Peek(7) == 0x187;
      assert s1.Peek(8) == 0x17a;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 99
    * Starting at 0x4e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x187

    requires s0.stack[4] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x187;
      assert s1.Peek(4) == 0x17a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s6, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 39
    * Starting at 0x187
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x187 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x17a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x17a;
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

  /** Node 68
    * Segment Id for this node is: 34
    * Starting at 0x154
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x015c);
      var s3 := Push2(s2, 0x02aa);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s4, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 52
    * Starting at 0x2aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Swap1(s7);
      var s9 := Div(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(1) == 0x15c;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s13, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 35
    * Starting at 0x15c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x15c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0169);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x03ef);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s8, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 74
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x169

    requires s0.stack[3] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x169;
      assert s1.Peek(3) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0402);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x402;
      assert s11.Peek(5) == 0x169;
      assert s11.Peek(6) == 0x15c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x03e0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s14, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 72
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x402

    requires s0.stack[6] == 0x169

    requires s0.stack[7] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x402;
      assert s1.Peek(6) == 0x169;
      assert s1.Peek(7) == 0x15c;
      var s2 := Push2(s1, 0x03e9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x03cf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s5, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 70
    * Starting at 0x3cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3e9

    requires s0.stack[4] == 0x402

    requires s0.stack[8] == 0x169

    requires s0.stack[9] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e9;
      assert s1.Peek(4) == 0x402;
      assert s1.Peek(8) == 0x169;
      assert s1.Peek(9) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03d9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s6, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3d9

    requires s0.stack[4] == 0x3e9

    requires s0.stack[7] == 0x402

    requires s0.stack[11] == 0x169

    requires s0.stack[12] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d9;
      assert s1.Peek(4) == 0x3e9;
      assert s1.Peek(7) == 0x402;
      assert s1.Peek(11) == 0x169;
      assert s1.Peek(12) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s6, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x3d9

    requires s0.stack[7] == 0x3e9

    requires s0.stack[10] == 0x402

    requires s0.stack[14] == 0x169

    requires s0.stack[15] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x3d9;
      assert s1.Peek(7) == 0x3e9;
      assert s1.Peek(10) == 0x402;
      assert s1.Peek(14) == 0x169;
      assert s1.Peek(15) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s8, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x3d9

    requires s0.stack[12] == 0x3e9

    requires s0.stack[15] == 0x402

    requires s0.stack[19] == 0x169

    requires s0.stack[20] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x3d9;
      assert s1.Peek(12) == 0x3e9;
      assert s1.Peek(15) == 0x402;
      assert s1.Peek(19) == 0x169;
      assert s1.Peek(20) == 0x15c;
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
      ExecuteFromCFGNode_s77(s11, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x169

    requires s0.stack[19] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x169;
      assert s1.Peek(19) == 0x15c;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s3, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x169

    requires s0.stack[19] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x169;
      assert s1.Peek(19) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s9, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x169

    requires s0.stack[18] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x169;
      assert s1.Peek(18) == 0x15c;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s3, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x169

    requires s0.stack[18] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x169;
      assert s1.Peek(18) == 0x15c;
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
      ExecuteFromCFGNode_s81(s11, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x3d9

    requires s0.stack[9] == 0x3e9

    requires s0.stack[12] == 0x402

    requires s0.stack[16] == 0x169

    requires s0.stack[17] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x3d9;
      assert s1.Peek(9) == 0x3e9;
      assert s1.Peek(12) == 0x402;
      assert s1.Peek(16) == 0x169;
      assert s1.Peek(17) == 0x15c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s7, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x3d9

    requires s0.stack[6] == 0x3e9

    requires s0.stack[9] == 0x402

    requires s0.stack[13] == 0x169

    requires s0.stack[14] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d9;
      assert s1.Peek(6) == 0x3e9;
      assert s1.Peek(9) == 0x402;
      assert s1.Peek(13) == 0x169;
      assert s1.Peek(14) == 0x15c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s7, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 71
    * Starting at 0x3d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3e9

    requires s0.stack[6] == 0x402

    requires s0.stack[10] == 0x169

    requires s0.stack[11] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e9;
      assert s1.Peek(6) == 0x402;
      assert s1.Peek(10) == 0x169;
      assert s1.Peek(11) == 0x15c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s7, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 73
    * Starting at 0x3e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x402

    requires s0.stack[7] == 0x169

    requires s0.stack[8] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x402;
      assert s1.Peek(7) == 0x169;
      assert s1.Peek(8) == 0x15c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 75
    * Starting at 0x402
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x169

    requires s0.stack[4] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x169;
      assert s1.Peek(4) == 0x15c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s6, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 36
    * Starting at 0x169
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x169 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x15c;
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

  /** Node 87
    * Segment Id for this node is: 31
    * Starting at 0x136
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x013e);
      var s3 := Push2(s2, 0x0285);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s4, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 51
    * Starting at 0x285
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x285 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x13e;
      var s2 := Push1(s1, 0x08);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x13e;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s14, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 32
    * Starting at 0x13e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x014b);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x049a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 92
    * Starting at 0x49a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x14b

    requires s0.stack[3] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14b;
      assert s1.Peek(3) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x04ad);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x4ad;
      assert s11.Peek(5) == 0x14b;
      assert s11.Peek(6) == 0x13e;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x048b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s14, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 90
    * Starting at 0x48b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x4ad

    requires s0.stack[6] == 0x14b

    requires s0.stack[7] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4ad;
      assert s1.Peek(6) == 0x14b;
      assert s1.Peek(7) == 0x13e;
      var s2 := Push2(s1, 0x0494);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x047a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s5, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 88
    * Starting at 0x47a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x494

    requires s0.stack[4] == 0x4ad

    requires s0.stack[8] == 0x14b

    requires s0.stack[9] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x494;
      assert s1.Peek(4) == 0x4ad;
      assert s1.Peek(8) == 0x14b;
      assert s1.Peek(9) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0484);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s6, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x484

    requires s0.stack[4] == 0x494

    requires s0.stack[7] == 0x4ad

    requires s0.stack[11] == 0x14b

    requires s0.stack[12] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x484;
      assert s1.Peek(4) == 0x494;
      assert s1.Peek(7) == 0x4ad;
      assert s1.Peek(11) == 0x14b;
      assert s1.Peek(12) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x484

    requires s0.stack[7] == 0x494

    requires s0.stack[10] == 0x4ad

    requires s0.stack[14] == 0x14b

    requires s0.stack[15] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x484;
      assert s1.Peek(7) == 0x494;
      assert s1.Peek(10) == 0x4ad;
      assert s1.Peek(14) == 0x14b;
      assert s1.Peek(15) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s8, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x484

    requires s0.stack[12] == 0x494

    requires s0.stack[15] == 0x4ad

    requires s0.stack[19] == 0x14b

    requires s0.stack[20] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x484;
      assert s1.Peek(12) == 0x494;
      assert s1.Peek(15) == 0x4ad;
      assert s1.Peek(19) == 0x14b;
      assert s1.Peek(20) == 0x13e;
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
      ExecuteFromCFGNode_s96(s11, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x484

    requires s0.stack[11] == 0x494

    requires s0.stack[14] == 0x4ad

    requires s0.stack[18] == 0x14b

    requires s0.stack[19] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x484;
      assert s1.Peek(11) == 0x494;
      assert s1.Peek(14) == 0x4ad;
      assert s1.Peek(18) == 0x14b;
      assert s1.Peek(19) == 0x13e;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s3, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x484

    requires s0.stack[11] == 0x494

    requires s0.stack[14] == 0x4ad

    requires s0.stack[18] == 0x14b

    requires s0.stack[19] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x484;
      assert s1.Peek(11) == 0x494;
      assert s1.Peek(14) == 0x4ad;
      assert s1.Peek(18) == 0x14b;
      assert s1.Peek(19) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s9, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x484

    requires s0.stack[10] == 0x494

    requires s0.stack[13] == 0x4ad

    requires s0.stack[17] == 0x14b

    requires s0.stack[18] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x484;
      assert s1.Peek(10) == 0x494;
      assert s1.Peek(13) == 0x4ad;
      assert s1.Peek(17) == 0x14b;
      assert s1.Peek(18) == 0x13e;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x484

    requires s0.stack[10] == 0x494

    requires s0.stack[13] == 0x4ad

    requires s0.stack[17] == 0x14b

    requires s0.stack[18] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x484;
      assert s1.Peek(10) == 0x494;
      assert s1.Peek(13) == 0x4ad;
      assert s1.Peek(17) == 0x14b;
      assert s1.Peek(18) == 0x13e;
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
      ExecuteFromCFGNode_s100(s11, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x484

    requires s0.stack[9] == 0x494

    requires s0.stack[12] == 0x4ad

    requires s0.stack[16] == 0x14b

    requires s0.stack[17] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x484;
      assert s1.Peek(9) == 0x494;
      assert s1.Peek(12) == 0x4ad;
      assert s1.Peek(16) == 0x14b;
      assert s1.Peek(17) == 0x13e;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s7, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x484

    requires s0.stack[6] == 0x494

    requires s0.stack[9] == 0x4ad

    requires s0.stack[13] == 0x14b

    requires s0.stack[14] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x484;
      assert s1.Peek(6) == 0x494;
      assert s1.Peek(9) == 0x4ad;
      assert s1.Peek(13) == 0x14b;
      assert s1.Peek(14) == 0x13e;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s7, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 89
    * Starting at 0x484
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x484 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x494

    requires s0.stack[6] == 0x4ad

    requires s0.stack[10] == 0x14b

    requires s0.stack[11] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x494;
      assert s1.Peek(6) == 0x4ad;
      assert s1.Peek(10) == 0x14b;
      assert s1.Peek(11) == 0x13e;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s7, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 91
    * Starting at 0x494
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x494 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x4ad

    requires s0.stack[7] == 0x14b

    requires s0.stack[8] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4ad;
      assert s1.Peek(7) == 0x14b;
      assert s1.Peek(8) == 0x13e;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 93
    * Starting at 0x4ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x14b

    requires s0.stack[4] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x14b;
      assert s1.Peek(4) == 0x13e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s6, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 33
    * Starting at 0x14b
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13e;
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

  /** Node 106
    * Segment Id for this node is: 10
    * Starting at 0x64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x3c76c784);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00a0);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s6, gas - 1)
      else
        ExecuteFromCFGNode_s107(s6, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 11
    * Starting at 0x70
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x4b2c7761);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00be);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s5, gas - 1)
      else
        ExecuteFromCFGNode_s108(s5, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 12
    * Starting at 0x7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x5b32619c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00dc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s5, gas - 1)
      else
        ExecuteFromCFGNode_s109(s5, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x6135a74e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00fa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s5, gas - 1)
      else
        ExecuteFromCFGNode_s110(s5, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 14
    * Starting at 0x91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x75ec402a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0118);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 28
    * Starting at 0x118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0120);
      var s3 := Push2(s2, 0x0260);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s4, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 50
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x120;
      var s2 := Push1(s1, 0x05);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x120;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 29
    * Starting at 0x120
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x120;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x012d);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0461);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s8, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 86
    * Starting at 0x461
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x461 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x12d

    requires s0.stack[3] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12d;
      assert s1.Peek(3) == 0x120;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0474);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x474;
      assert s11.Peek(5) == 0x12d;
      assert s11.Peek(6) == 0x120;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0452);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s14, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 84
    * Starting at 0x452
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x474

    requires s0.stack[6] == 0x12d

    requires s0.stack[7] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x474;
      assert s1.Peek(6) == 0x12d;
      assert s1.Peek(7) == 0x120;
      var s2 := Push2(s1, 0x045b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0441);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s5, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 82
    * Starting at 0x441
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x441 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x45b

    requires s0.stack[4] == 0x474

    requires s0.stack[8] == 0x12d

    requires s0.stack[9] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x45b;
      assert s1.Peek(4) == 0x474;
      assert s1.Peek(8) == 0x12d;
      assert s1.Peek(9) == 0x120;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x044b);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s6, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x44b

    requires s0.stack[4] == 0x45b

    requires s0.stack[7] == 0x474

    requires s0.stack[11] == 0x12d

    requires s0.stack[12] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x44b;
      assert s1.Peek(4) == 0x45b;
      assert s1.Peek(7) == 0x474;
      assert s1.Peek(11) == 0x12d;
      assert s1.Peek(12) == 0x120;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s6, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x44b

    requires s0.stack[7] == 0x45b

    requires s0.stack[10] == 0x474

    requires s0.stack[14] == 0x12d

    requires s0.stack[15] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x44b;
      assert s1.Peek(7) == 0x45b;
      assert s1.Peek(10) == 0x474;
      assert s1.Peek(14) == 0x12d;
      assert s1.Peek(15) == 0x120;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s8, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x44b

    requires s0.stack[12] == 0x45b

    requires s0.stack[15] == 0x474

    requires s0.stack[19] == 0x12d

    requires s0.stack[20] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x44b;
      assert s1.Peek(12) == 0x45b;
      assert s1.Peek(15) == 0x474;
      assert s1.Peek(19) == 0x12d;
      assert s1.Peek(20) == 0x120;
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
      ExecuteFromCFGNode_s120(s11, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x44b

    requires s0.stack[11] == 0x45b

    requires s0.stack[14] == 0x474

    requires s0.stack[18] == 0x12d

    requires s0.stack[19] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x44b;
      assert s1.Peek(11) == 0x45b;
      assert s1.Peek(14) == 0x474;
      assert s1.Peek(18) == 0x12d;
      assert s1.Peek(19) == 0x120;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s3, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x44b

    requires s0.stack[11] == 0x45b

    requires s0.stack[14] == 0x474

    requires s0.stack[18] == 0x12d

    requires s0.stack[19] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x44b;
      assert s1.Peek(11) == 0x45b;
      assert s1.Peek(14) == 0x474;
      assert s1.Peek(18) == 0x12d;
      assert s1.Peek(19) == 0x120;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s9, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x44b

    requires s0.stack[10] == 0x45b

    requires s0.stack[13] == 0x474

    requires s0.stack[17] == 0x12d

    requires s0.stack[18] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x44b;
      assert s1.Peek(10) == 0x45b;
      assert s1.Peek(13) == 0x474;
      assert s1.Peek(17) == 0x12d;
      assert s1.Peek(18) == 0x120;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x44b

    requires s0.stack[10] == 0x45b

    requires s0.stack[13] == 0x474

    requires s0.stack[17] == 0x12d

    requires s0.stack[18] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x44b;
      assert s1.Peek(10) == 0x45b;
      assert s1.Peek(13) == 0x474;
      assert s1.Peek(17) == 0x12d;
      assert s1.Peek(18) == 0x120;
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
      ExecuteFromCFGNode_s124(s11, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x44b

    requires s0.stack[9] == 0x45b

    requires s0.stack[12] == 0x474

    requires s0.stack[16] == 0x12d

    requires s0.stack[17] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x44b;
      assert s1.Peek(9) == 0x45b;
      assert s1.Peek(12) == 0x474;
      assert s1.Peek(16) == 0x12d;
      assert s1.Peek(17) == 0x120;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s7, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x44b

    requires s0.stack[6] == 0x45b

    requires s0.stack[9] == 0x474

    requires s0.stack[13] == 0x12d

    requires s0.stack[14] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x44b;
      assert s1.Peek(6) == 0x45b;
      assert s1.Peek(9) == 0x474;
      assert s1.Peek(13) == 0x12d;
      assert s1.Peek(14) == 0x120;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s7, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 83
    * Starting at 0x44b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x45b

    requires s0.stack[6] == 0x474

    requires s0.stack[10] == 0x12d

    requires s0.stack[11] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x45b;
      assert s1.Peek(6) == 0x474;
      assert s1.Peek(10) == 0x12d;
      assert s1.Peek(11) == 0x120;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s7, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 85
    * Starting at 0x45b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x474

    requires s0.stack[7] == 0x12d

    requires s0.stack[8] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x474;
      assert s1.Peek(7) == 0x12d;
      assert s1.Peek(8) == 0x120;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s6, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 87
    * Starting at 0x474
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x474 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x12d

    requires s0.stack[4] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12d;
      assert s1.Peek(4) == 0x120;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s6, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 30
    * Starting at 0x12d
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x120

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x120;
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

  /** Node 130
    * Segment Id for this node is: 25
    * Starting at 0xfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0102);
      var s3 := Push2(s2, 0x023b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s4, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 49
    * Starting at 0x23b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x102;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s14, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 26
    * Starting at 0x102
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x010f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x03ef);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s8, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 74
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x10f

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10f;
      assert s1.Peek(3) == 0x102;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0402);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x402;
      assert s11.Peek(5) == 0x10f;
      assert s11.Peek(6) == 0x102;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x03e0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s14, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 72
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x402

    requires s0.stack[6] == 0x10f

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x402;
      assert s1.Peek(6) == 0x10f;
      assert s1.Peek(7) == 0x102;
      var s2 := Push2(s1, 0x03e9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x03cf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 70
    * Starting at 0x3cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3e9

    requires s0.stack[4] == 0x402

    requires s0.stack[8] == 0x10f

    requires s0.stack[9] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e9;
      assert s1.Peek(4) == 0x402;
      assert s1.Peek(8) == 0x10f;
      assert s1.Peek(9) == 0x102;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03d9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s6, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3d9

    requires s0.stack[4] == 0x3e9

    requires s0.stack[7] == 0x402

    requires s0.stack[11] == 0x10f

    requires s0.stack[12] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d9;
      assert s1.Peek(4) == 0x3e9;
      assert s1.Peek(7) == 0x402;
      assert s1.Peek(11) == 0x10f;
      assert s1.Peek(12) == 0x102;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s6, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x3d9

    requires s0.stack[7] == 0x3e9

    requires s0.stack[10] == 0x402

    requires s0.stack[14] == 0x10f

    requires s0.stack[15] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x3d9;
      assert s1.Peek(7) == 0x3e9;
      assert s1.Peek(10) == 0x402;
      assert s1.Peek(14) == 0x10f;
      assert s1.Peek(15) == 0x102;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s8, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x3d9

    requires s0.stack[12] == 0x3e9

    requires s0.stack[15] == 0x402

    requires s0.stack[19] == 0x10f

    requires s0.stack[20] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x3d9;
      assert s1.Peek(12) == 0x3e9;
      assert s1.Peek(15) == 0x402;
      assert s1.Peek(19) == 0x10f;
      assert s1.Peek(20) == 0x102;
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
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x10f

    requires s0.stack[19] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x10f;
      assert s1.Peek(19) == 0x102;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s3, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0x10f

    requires s0.stack[19] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0x10f;
      assert s1.Peek(19) == 0x102;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s9, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x10f

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x10f;
      assert s1.Peek(18) == 0x102;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s3, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0x10f

    requires s0.stack[18] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0x10f;
      assert s1.Peek(18) == 0x102;
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
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x3d9

    requires s0.stack[9] == 0x3e9

    requires s0.stack[12] == 0x402

    requires s0.stack[16] == 0x10f

    requires s0.stack[17] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x3d9;
      assert s1.Peek(9) == 0x3e9;
      assert s1.Peek(12) == 0x402;
      assert s1.Peek(16) == 0x10f;
      assert s1.Peek(17) == 0x102;
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
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x3d9

    requires s0.stack[6] == 0x3e9

    requires s0.stack[9] == 0x402

    requires s0.stack[13] == 0x10f

    requires s0.stack[14] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d9;
      assert s1.Peek(6) == 0x3e9;
      assert s1.Peek(9) == 0x402;
      assert s1.Peek(13) == 0x10f;
      assert s1.Peek(14) == 0x102;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s7, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 71
    * Starting at 0x3d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3e9

    requires s0.stack[6] == 0x402

    requires s0.stack[10] == 0x10f

    requires s0.stack[11] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e9;
      assert s1.Peek(6) == 0x402;
      assert s1.Peek(10) == 0x10f;
      assert s1.Peek(11) == 0x102;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s7, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 73
    * Starting at 0x3e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x402

    requires s0.stack[7] == 0x10f

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x402;
      assert s1.Peek(7) == 0x10f;
      assert s1.Peek(8) == 0x102;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s6, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 75
    * Starting at 0x402
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x10f

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10f;
      assert s1.Peek(4) == 0x102;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s6, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 27
    * Starting at 0x10f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x102;
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

  /** Node 149
    * Segment Id for this node is: 22
    * Starting at 0xdc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e4);
      var s3 := Push2(s2, 0x0216);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s4, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 48
    * Starting at 0x216
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe4;
      var s2 := Push1(s1, 0x09);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0xe4;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s14, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 23
    * Starting at 0xe4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe4;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00f1);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0428);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s8, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 80
    * Starting at 0x428
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x428 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xf1

    requires s0.stack[3] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf1;
      assert s1.Peek(3) == 0xe4;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x043b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x43b;
      assert s11.Peek(5) == 0xf1;
      assert s11.Peek(6) == 0xe4;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0419);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s14, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 78
    * Starting at 0x419
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x419 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x43b

    requires s0.stack[6] == 0xf1

    requires s0.stack[7] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x43b;
      assert s1.Peek(6) == 0xf1;
      assert s1.Peek(7) == 0xe4;
      var s2 := Push2(s1, 0x0422);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0408);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s5, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 76
    * Starting at 0x408
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x422

    requires s0.stack[4] == 0x43b

    requires s0.stack[8] == 0xf1

    requires s0.stack[9] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x422;
      assert s1.Peek(4) == 0x43b;
      assert s1.Peek(8) == 0xf1;
      assert s1.Peek(9) == 0xe4;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0412);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s6, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x412

    requires s0.stack[4] == 0x422

    requires s0.stack[7] == 0x43b

    requires s0.stack[11] == 0xf1

    requires s0.stack[12] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x412;
      assert s1.Peek(4) == 0x422;
      assert s1.Peek(7) == 0x43b;
      assert s1.Peek(11) == 0xf1;
      assert s1.Peek(12) == 0xe4;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x412

    requires s0.stack[7] == 0x422

    requires s0.stack[10] == 0x43b

    requires s0.stack[14] == 0xf1

    requires s0.stack[15] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x412;
      assert s1.Peek(7) == 0x422;
      assert s1.Peek(10) == 0x43b;
      assert s1.Peek(14) == 0xf1;
      assert s1.Peek(15) == 0xe4;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s8, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x412

    requires s0.stack[12] == 0x422

    requires s0.stack[15] == 0x43b

    requires s0.stack[19] == 0xf1

    requires s0.stack[20] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x412;
      assert s1.Peek(12) == 0x422;
      assert s1.Peek(15) == 0x43b;
      assert s1.Peek(19) == 0xf1;
      assert s1.Peek(20) == 0xe4;
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
      ExecuteFromCFGNode_s158(s11, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x412

    requires s0.stack[11] == 0x422

    requires s0.stack[14] == 0x43b

    requires s0.stack[18] == 0xf1

    requires s0.stack[19] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x412;
      assert s1.Peek(11) == 0x422;
      assert s1.Peek(14) == 0x43b;
      assert s1.Peek(18) == 0xf1;
      assert s1.Peek(19) == 0xe4;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s3, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x412

    requires s0.stack[11] == 0x422

    requires s0.stack[14] == 0x43b

    requires s0.stack[18] == 0xf1

    requires s0.stack[19] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x412;
      assert s1.Peek(11) == 0x422;
      assert s1.Peek(14) == 0x43b;
      assert s1.Peek(18) == 0xf1;
      assert s1.Peek(19) == 0xe4;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s9, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x412

    requires s0.stack[10] == 0x422

    requires s0.stack[13] == 0x43b

    requires s0.stack[17] == 0xf1

    requires s0.stack[18] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x412;
      assert s1.Peek(10) == 0x422;
      assert s1.Peek(13) == 0x43b;
      assert s1.Peek(17) == 0xf1;
      assert s1.Peek(18) == 0xe4;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s3, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x412

    requires s0.stack[10] == 0x422

    requires s0.stack[13] == 0x43b

    requires s0.stack[17] == 0xf1

    requires s0.stack[18] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x412;
      assert s1.Peek(10) == 0x422;
      assert s1.Peek(13) == 0x43b;
      assert s1.Peek(17) == 0xf1;
      assert s1.Peek(18) == 0xe4;
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
      ExecuteFromCFGNode_s162(s11, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x412

    requires s0.stack[9] == 0x422

    requires s0.stack[12] == 0x43b

    requires s0.stack[16] == 0xf1

    requires s0.stack[17] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x412;
      assert s1.Peek(9) == 0x422;
      assert s1.Peek(12) == 0x43b;
      assert s1.Peek(16) == 0xf1;
      assert s1.Peek(17) == 0xe4;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s7, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x412

    requires s0.stack[6] == 0x422

    requires s0.stack[9] == 0x43b

    requires s0.stack[13] == 0xf1

    requires s0.stack[14] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x412;
      assert s1.Peek(6) == 0x422;
      assert s1.Peek(9) == 0x43b;
      assert s1.Peek(13) == 0xf1;
      assert s1.Peek(14) == 0xe4;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s7, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 77
    * Starting at 0x412
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x412 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x422

    requires s0.stack[6] == 0x43b

    requires s0.stack[10] == 0xf1

    requires s0.stack[11] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x422;
      assert s1.Peek(6) == 0x43b;
      assert s1.Peek(10) == 0xf1;
      assert s1.Peek(11) == 0xe4;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s7, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 79
    * Starting at 0x422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x43b

    requires s0.stack[7] == 0xf1

    requires s0.stack[8] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x43b;
      assert s1.Peek(7) == 0xf1;
      assert s1.Peek(8) == 0xe4;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s6, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 81
    * Starting at 0x43b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xf1

    requires s0.stack[4] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf1;
      assert s1.Peek(4) == 0xe4;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s6, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 24
    * Starting at 0xf1
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe4;
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

  /** Node 168
    * Segment Id for this node is: 19
    * Starting at 0xbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00c6);
      var s3 := Push2(s2, 0x01f1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s4, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 47
    * Starting at 0x1f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc6;
      var s2 := Push1(s1, 0x01);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0xc6;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s14, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 20
    * Starting at 0xc6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00d3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x03ef);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s8, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 74
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xd3

    requires s0.stack[3] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3;
      assert s1.Peek(3) == 0xc6;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0402);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x402;
      assert s11.Peek(5) == 0xd3;
      assert s11.Peek(6) == 0xc6;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x03e0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s14, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 72
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x402

    requires s0.stack[6] == 0xd3

    requires s0.stack[7] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x402;
      assert s1.Peek(6) == 0xd3;
      assert s1.Peek(7) == 0xc6;
      var s2 := Push2(s1, 0x03e9);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x03cf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 70
    * Starting at 0x3cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3e9

    requires s0.stack[4] == 0x402

    requires s0.stack[8] == 0xd3

    requires s0.stack[9] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3e9;
      assert s1.Peek(4) == 0x402;
      assert s1.Peek(8) == 0xd3;
      assert s1.Peek(9) == 0xc6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03d9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s6, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3d9

    requires s0.stack[4] == 0x3e9

    requires s0.stack[7] == 0x402

    requires s0.stack[11] == 0xd3

    requires s0.stack[12] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3d9;
      assert s1.Peek(4) == 0x3e9;
      assert s1.Peek(7) == 0x402;
      assert s1.Peek(11) == 0xd3;
      assert s1.Peek(12) == 0xc6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s6, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x3d9

    requires s0.stack[7] == 0x3e9

    requires s0.stack[10] == 0x402

    requires s0.stack[14] == 0xd3

    requires s0.stack[15] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x3d9;
      assert s1.Peek(7) == 0x3e9;
      assert s1.Peek(10) == 0x402;
      assert s1.Peek(14) == 0xd3;
      assert s1.Peek(15) == 0xc6;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s8, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x3d9

    requires s0.stack[12] == 0x3e9

    requires s0.stack[15] == 0x402

    requires s0.stack[19] == 0xd3

    requires s0.stack[20] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x3d9;
      assert s1.Peek(12) == 0x3e9;
      assert s1.Peek(15) == 0x402;
      assert s1.Peek(19) == 0xd3;
      assert s1.Peek(20) == 0xc6;
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
      ExecuteFromCFGNode_s177(s11, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0xd3

    requires s0.stack[19] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0xd3;
      assert s1.Peek(19) == 0xc6;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s3, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3d9

    requires s0.stack[11] == 0x3e9

    requires s0.stack[14] == 0x402

    requires s0.stack[18] == 0xd3

    requires s0.stack[19] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3d9;
      assert s1.Peek(11) == 0x3e9;
      assert s1.Peek(14) == 0x402;
      assert s1.Peek(18) == 0xd3;
      assert s1.Peek(19) == 0xc6;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s9, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0xd3;
      assert s1.Peek(18) == 0xc6;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s3, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3d9

    requires s0.stack[10] == 0x3e9

    requires s0.stack[13] == 0x402

    requires s0.stack[17] == 0xd3

    requires s0.stack[18] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3d9;
      assert s1.Peek(10) == 0x3e9;
      assert s1.Peek(13) == 0x402;
      assert s1.Peek(17) == 0xd3;
      assert s1.Peek(18) == 0xc6;
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
      ExecuteFromCFGNode_s181(s11, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x3d9

    requires s0.stack[9] == 0x3e9

    requires s0.stack[12] == 0x402

    requires s0.stack[16] == 0xd3

    requires s0.stack[17] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x3d9;
      assert s1.Peek(9) == 0x3e9;
      assert s1.Peek(12) == 0x402;
      assert s1.Peek(16) == 0xd3;
      assert s1.Peek(17) == 0xc6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x3d9

    requires s0.stack[6] == 0x3e9

    requires s0.stack[9] == 0x402

    requires s0.stack[13] == 0xd3

    requires s0.stack[14] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d9;
      assert s1.Peek(6) == 0x3e9;
      assert s1.Peek(9) == 0x402;
      assert s1.Peek(13) == 0xd3;
      assert s1.Peek(14) == 0xc6;
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
    * Segment Id for this node is: 71
    * Starting at 0x3d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3e9

    requires s0.stack[6] == 0x402

    requires s0.stack[10] == 0xd3

    requires s0.stack[11] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e9;
      assert s1.Peek(6) == 0x402;
      assert s1.Peek(10) == 0xd3;
      assert s1.Peek(11) == 0xc6;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s7, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 73
    * Starting at 0x3e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x402

    requires s0.stack[7] == 0xd3

    requires s0.stack[8] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x402;
      assert s1.Peek(7) == 0xd3;
      assert s1.Peek(8) == 0xc6;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 75
    * Starting at 0x402
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x402 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xd3

    requires s0.stack[4] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3;
      assert s1.Peek(4) == 0xc6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s6, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 21
    * Starting at 0xd3
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xc6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6;
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

  /** Node 187
    * Segment Id for this node is: 16
    * Starting at 0xa0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00a8);
      var s3 := Push2(s2, 0x01cc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s4, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 46
    * Starting at 0x1cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8;
      var s2 := Push1(s1, 0x07);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0xa8;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s14, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 17
    * Starting at 0xa8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00b5);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x03b6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s8, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 68
    * Starting at 0x3b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xb5

    requires s0.stack[3] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb5;
      assert s1.Peek(3) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x03c9);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x3c9;
      assert s11.Peek(5) == 0xb5;
      assert s11.Peek(6) == 0xa8;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x03a7);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s14, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 66
    * Starting at 0x3a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x3c9

    requires s0.stack[6] == 0xb5

    requires s0.stack[7] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c9;
      assert s1.Peek(6) == 0xb5;
      assert s1.Peek(7) == 0xa8;
      var s2 := Push2(s1, 0x03b0);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0396);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s5, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 64
    * Starting at 0x396
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3b0

    requires s0.stack[4] == 0x3c9

    requires s0.stack[8] == 0xb5

    requires s0.stack[9] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b0;
      assert s1.Peek(4) == 0x3c9;
      assert s1.Peek(8) == 0xb5;
      assert s1.Peek(9) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x03a0);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0385);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s6, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 62
    * Starting at 0x385
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3a0

    requires s0.stack[4] == 0x3b0

    requires s0.stack[7] == 0x3c9

    requires s0.stack[11] == 0xb5

    requires s0.stack[12] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a0;
      assert s1.Peek(4) == 0x3b0;
      assert s1.Peek(7) == 0x3c9;
      assert s1.Peek(11) == 0xb5;
      assert s1.Peek(12) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x038f);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0364);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s6, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 58
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x38f

    requires s0.stack[4] == 0x3a0

    requires s0.stack[7] == 0x3b0

    requires s0.stack[10] == 0x3c9

    requires s0.stack[14] == 0xb5

    requires s0.stack[15] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x38f;
      assert s1.Peek(4) == 0x3a0;
      assert s1.Peek(7) == 0x3b0;
      assert s1.Peek(10) == 0x3c9;
      assert s1.Peek(14) == 0xb5;
      assert s1.Peek(15) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x037e);
      var s4 := Push2(s3, 0x0379);
      var s5 := Push2(s4, 0x0374);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s8, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x374

    requires s0.stack[2] == 0x379

    requires s0.stack[3] == 0x37e

    requires s0.stack[6] == 0x38f

    requires s0.stack[9] == 0x3a0

    requires s0.stack[12] == 0x3b0

    requires s0.stack[15] == 0x3c9

    requires s0.stack[19] == 0xb5

    requires s0.stack[20] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x374;
      assert s1.Peek(2) == 0x379;
      assert s1.Peek(3) == 0x37e;
      assert s1.Peek(6) == 0x38f;
      assert s1.Peek(9) == 0x3a0;
      assert s1.Peek(12) == 0x3b0;
      assert s1.Peek(15) == 0x3c9;
      assert s1.Peek(19) == 0xb5;
      assert s1.Peek(20) == 0xa8;
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
      ExecuteFromCFGNode_s196(s11, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 59
    * Starting at 0x374
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x374 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3a0

    requires s0.stack[11] == 0x3b0

    requires s0.stack[14] == 0x3c9

    requires s0.stack[18] == 0xb5

    requires s0.stack[19] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3a0;
      assert s1.Peek(11) == 0x3b0;
      assert s1.Peek(14) == 0x3c9;
      assert s1.Peek(18) == 0xb5;
      assert s1.Peek(19) == 0xa8;
      var s2 := Push2(s1, 0x035b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s3, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 57
    * Starting at 0x35b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x379

    requires s0.stack[2] == 0x37e

    requires s0.stack[5] == 0x38f

    requires s0.stack[8] == 0x3a0

    requires s0.stack[11] == 0x3b0

    requires s0.stack[14] == 0x3c9

    requires s0.stack[18] == 0xb5

    requires s0.stack[19] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x379;
      assert s1.Peek(2) == 0x37e;
      assert s1.Peek(5) == 0x38f;
      assert s1.Peek(8) == 0x3a0;
      assert s1.Peek(11) == 0x3b0;
      assert s1.Peek(14) == 0x3c9;
      assert s1.Peek(18) == 0xb5;
      assert s1.Peek(19) == 0xa8;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s9, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 60
    * Starting at 0x379
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x379 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3a0

    requires s0.stack[10] == 0x3b0

    requires s0.stack[13] == 0x3c9

    requires s0.stack[17] == 0xb5

    requires s0.stack[18] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3a0;
      assert s1.Peek(10) == 0x3b0;
      assert s1.Peek(13) == 0x3c9;
      assert s1.Peek(17) == 0xb5;
      assert s1.Peek(18) == 0xa8;
      var s2 := Push2(s1, 0x033c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s3, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 56
    * Starting at 0x33c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x37e

    requires s0.stack[4] == 0x38f

    requires s0.stack[7] == 0x3a0

    requires s0.stack[10] == 0x3b0

    requires s0.stack[13] == 0x3c9

    requires s0.stack[17] == 0xb5

    requires s0.stack[18] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37e;
      assert s1.Peek(4) == 0x38f;
      assert s1.Peek(7) == 0x3a0;
      assert s1.Peek(10) == 0x3b0;
      assert s1.Peek(13) == 0x3c9;
      assert s1.Peek(17) == 0xb5;
      assert s1.Peek(18) == 0xa8;
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
      ExecuteFromCFGNode_s200(s11, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 61
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x38f

    requires s0.stack[6] == 0x3a0

    requires s0.stack[9] == 0x3b0

    requires s0.stack[12] == 0x3c9

    requires s0.stack[16] == 0xb5

    requires s0.stack[17] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x38f;
      assert s1.Peek(6) == 0x3a0;
      assert s1.Peek(9) == 0x3b0;
      assert s1.Peek(12) == 0x3c9;
      assert s1.Peek(16) == 0xb5;
      assert s1.Peek(17) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s7, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 63
    * Starting at 0x38f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x3a0

    requires s0.stack[6] == 0x3b0

    requires s0.stack[9] == 0x3c9

    requires s0.stack[13] == 0xb5

    requires s0.stack[14] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3a0;
      assert s1.Peek(6) == 0x3b0;
      assert s1.Peek(9) == 0x3c9;
      assert s1.Peek(13) == 0xb5;
      assert s1.Peek(14) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s7, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 65
    * Starting at 0x3a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3b0

    requires s0.stack[6] == 0x3c9

    requires s0.stack[10] == 0xb5

    requires s0.stack[11] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b0;
      assert s1.Peek(6) == 0x3c9;
      assert s1.Peek(10) == 0xb5;
      assert s1.Peek(11) == 0xa8;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s7, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 67
    * Starting at 0x3b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c9

    requires s0.stack[7] == 0xb5

    requires s0.stack[8] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3c9;
      assert s1.Peek(7) == 0xb5;
      assert s1.Peek(8) == 0xa8;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s6, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 69
    * Starting at 0x3c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xb5

    requires s0.stack[4] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb5;
      assert s1.Peek(4) == 0xa8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s6, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 18
    * Starting at 0xb5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xa8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa8;
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

  /** Node 206
    * Segment Id for this node is: 15
    * Starting at 0x9c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c as nat
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
