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
      var s6 := Push2(s5, 0x00b5);
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
      var s6 := Push4(s5, 0x70a08231);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x007d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s9, gas - 1)
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
      var s2 := Push4(s1, 0xc70bb216);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0058);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc70bb216);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0177);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd0665518);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01a2);
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
      var s4 := Push2(s3, 0x01b7);
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
    * Segment Id for this node is: 40
    * Starting at 0x1b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00fe);
      var s3 := Push2(s2, 0x01c5);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x08f4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s7, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 131
    * Starting at 0x8f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1c5

    requires s0.stack[3] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c5;
      assert s1.Peek(3) == 0xfe;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0905);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s11, gas - 1)
      else
        ExecuteFromCFGNode_s11(s11, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 132
    * Starting at 0x902
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x902 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c5

    requires s0.stack[5] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x1c5;
      assert s1.Peek(6) == 0xfe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 12
    * Segment Id for this node is: 133
    * Starting at 0x905
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x905 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c5

    requires s0.stack[5] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c5;
      assert s1.Peek(5) == 0xfe;
      var s2 := Push2(s1, 0x090e);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x078b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s5, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x90e

    requires s0.stack[6] == 0x1c5

    requires s0.stack[7] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x90e;
      assert s1.Peek(6) == 0x1c5;
      assert s1.Peek(7) == 0xfe;
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
      assert s11.Peek(4) == 0x90e;
      assert s11.Peek(9) == 0x1c5;
      assert s11.Peek(10) == 0xfe;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s14, gas - 1)
      else
        ExecuteFromCFGNode_s14(s14, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x90e

    requires s0.stack[7] == 0x1c5

    requires s0.stack[8] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x90e;
      assert s1.Peek(8) == 0x1c5;
      assert s1.Peek(9) == 0xfe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 15
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x90e

    requires s0.stack[7] == 0x1c5

    requires s0.stack[8] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x90e;
      assert s1.Peek(7) == 0x1c5;
      assert s1.Peek(8) == 0xfe;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s5, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 134
    * Starting at 0x90e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c5

    requires s0.stack[6] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c5;
      assert s1.Peek(6) == 0xfe;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x091c);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x078b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s9, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x91c

    requires s0.stack[6] == 0x1c5

    requires s0.stack[7] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x91c;
      assert s1.Peek(6) == 0x1c5;
      assert s1.Peek(7) == 0xfe;
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
      assert s11.Peek(4) == 0x91c;
      assert s11.Peek(9) == 0x1c5;
      assert s11.Peek(10) == 0xfe;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s14, gas - 1)
      else
        ExecuteFromCFGNode_s18(s14, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x91c

    requires s0.stack[7] == 0x1c5

    requires s0.stack[8] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x91c;
      assert s1.Peek(8) == 0x1c5;
      assert s1.Peek(9) == 0xfe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 19
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x91c

    requires s0.stack[7] == 0x1c5

    requires s0.stack[8] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x91c;
      assert s1.Peek(7) == 0x1c5;
      assert s1.Peek(8) == 0xfe;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s5, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 135
    * Starting at 0x91c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c5

    requires s0.stack[6] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c5;
      assert s1.Peek(6) == 0xfe;
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
    * Segment Id for this node is: 41
    * Starting at 0x1c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfe;
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
      assert s11.Peek(4) == 0xfe;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0xfe;
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
      assert s31.Peek(4) == 0xfe;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s36, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 26
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
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
      var s9 := Push2(s8, 0x00ce);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s10, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 21
    * Starting at 0xce
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
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
    * Segment Id for this node is: 37
    * Starting at 0x1a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01b5);
      var s3 := Push2(s2, 0x01b0);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0834);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s7, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 114
    * Starting at 0x834
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x834 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1b0

    requires s0.stack[3] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b0;
      assert s1.Peek(3) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0845);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s11, gas - 1)
      else
        ExecuteFromCFGNode_s26(s11, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 115
    * Starting at 0x842
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x842 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1b0

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x1b0;
      assert s1.Peek(6) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 27
    * Segment Id for this node is: 116
    * Starting at 0x845
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x845 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1b0

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b0;
      assert s1.Peek(5) == 0x1b5;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x085c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s10, gas - 1)
      else
        ExecuteFromCFGNode_s28(s10, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 117
    * Starting at 0x859
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x859 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1b0

    requires s0.stack[7] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x1b0;
      assert s1.Peek(8) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 29
    * Segment Id for this node is: 118
    * Starting at 0x85c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1b0

    requires s0.stack[7] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1b0;
      assert s1.Peek(7) == 0x1b5;
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
      assert s11.Peek(7) == 0x1b0;
      assert s11.Peek(8) == 0x1b5;
      var s12 := Push2(s11, 0x086f);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s13, gas - 1)
      else
        ExecuteFromCFGNode_s30(s13, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 119
    * Starting at 0x86c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1b0

    requires s0.stack[7] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(7) == 0x1b0;
      assert s1.Peek(8) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 31
    * Segment Id for this node is: 120
    * Starting at 0x86f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1b0

    requires s0.stack[7] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1b0;
      assert s1.Peek(7) == 0x1b5;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0881);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s9, gas - 1)
      else
        ExecuteFromCFGNode_s32(s9, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 121
    * Starting at 0x87a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x1b0

    requires s0.stack[8] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0881);
      assert s1.Peek(0) == 0x881;
      assert s1.Peek(8) == 0x1b0;
      assert s1.Peek(9) == 0x1b5;
      var s2 := Push2(s1, 0x0820);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s3, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 113
    * Starting at 0x820
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x820 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x881

    requires s0.stack[8] == 0x1b0

    requires s0.stack[9] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x881;
      assert s1.Peek(8) == 0x1b0;
      assert s1.Peek(9) == 0x1b5;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x881;
      assert s11.Peek(10) == 0x1b0;
      assert s11.Peek(11) == 0x1b5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 34
    * Segment Id for this node is: 122
    * Starting at 0x881
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x881 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x1b0

    requires s0.stack[8] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1b0;
      assert s1.Peek(8) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := Push1(s8, 0x3f);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(11) == 0x1b0;
      assert s11.Peek(12) == 0x1b5;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Add(s13);
      var s15 := Dup2(s14);
      var s16 := Dup2(s15);
      var s17 := Lt(s16);
      var s18 := Dup6(s17);
      var s19 := Dup3(s18);
      var s20 := Gt(s19);
      var s21 := Or(s20);
      assert s21.Peek(11) == 0x1b0;
      assert s21.Peek(12) == 0x1b5;
      var s22 := IsZero(s21);
      var s23 := Push2(s22, 0x08a6);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s24, gas - 1)
      else
        ExecuteFromCFGNode_s35(s24, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 123
    * Starting at 0x89f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x1b0

    requires s0.stack[11] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08a6);
      assert s1.Peek(0) == 0x8a6;
      assert s1.Peek(11) == 0x1b0;
      assert s1.Peek(12) == 0x1b5;
      var s2 := Push2(s1, 0x0820);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 113
    * Starting at 0x820
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x820 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x8a6

    requires s0.stack[11] == 0x1b0

    requires s0.stack[12] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8a6;
      assert s1.Peek(11) == 0x1b0;
      assert s1.Peek(12) == 0x1b5;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x8a6;
      assert s11.Peek(13) == 0x1b0;
      assert s11.Peek(14) == 0x1b5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 37
    * Segment Id for this node is: 124
    * Starting at 0x8a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x1b0

    requires s0.stack[11] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x1b0;
      assert s1.Peek(11) == 0x1b5;
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
      assert s11.Peek(8) == 0x1b0;
      assert s11.Peek(9) == 0x1b5;
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
      assert s21.Peek(10) == 0x1b0;
      assert s21.Peek(11) == 0x1b5;
      var s22 := Push2(s21, 0x08c3);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s23, gas - 1)
      else
        ExecuteFromCFGNode_s38(s23, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 125
    * Starting at 0x8c0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1b0

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(10) == 0x1b0;
      assert s1.Peek(11) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 39
    * Segment Id for this node is: 126
    * Starting at 0x8c3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1b0

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x1b0;
      assert s1.Peek(10) == 0x1b5;
      var s2 := Swap4(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap4(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s5, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 127
    * Starting at 0x8c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1b0

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x1b0;
      assert s1.Peek(10) == 0x1b5;
      var s2 := Dup3(s1);
      var s3 := Dup6(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08e8);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s7, gas - 1)
      else
        ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 128
    * Starting at 0x8d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1b0

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08d9);
      assert s1.Peek(0) == 0x8d9;
      assert s1.Peek(10) == 0x1b0;
      assert s1.Peek(11) == 0x1b5;
      var s2 := Dup6(s1);
      var s3 := Push2(s2, 0x078b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s4, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x8d9

    requires s0.stack[11] == 0x1b0

    requires s0.stack[12] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8d9;
      assert s1.Peek(11) == 0x1b0;
      assert s1.Peek(12) == 0x1b5;
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
      assert s11.Peek(4) == 0x8d9;
      assert s11.Peek(14) == 0x1b0;
      assert s11.Peek(15) == 0x1b5;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s14, gas - 1)
      else
        ExecuteFromCFGNode_s43(s14, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x8d9

    requires s0.stack[12] == 0x1b0

    requires s0.stack[13] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x8d9;
      assert s1.Peek(13) == 0x1b0;
      assert s1.Peek(14) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 44
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x8d9

    requires s0.stack[12] == 0x1b0

    requires s0.stack[13] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8d9;
      assert s1.Peek(12) == 0x1b0;
      assert s1.Peek(13) == 0x1b5;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s5, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 129
    * Starting at 0x8d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[10] == 0x1b0

    requires s0.stack[11] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x1b0;
      assert s1.Peek(11) == 0x1b5;
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
      assert s11.Peek(9) == 0x1b0;
      assert s11.Peek(10) == 0x1b5;
      var s12 := Push2(s11, 0x08c8);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s13, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 130
    * Starting at 0x8e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x1b0

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x1b0;
      assert s1.Peek(10) == 0x1b5;
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
      assert s11.Peek(0) == 0x1b0;
      assert s11.Peek(2) == 0x1b5;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s12, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 38
    * Starting at 0x1b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b5;
      var s2 := Push2(s1, 0x0317);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s3, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 61
    * Starting at 0x317
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x317 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b5;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(2) == 0x1b5;
      var s12 := Push2(s11, 0x0364);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s13, gas - 1)
      else
        ExecuteFromCFGNode_s49(s13, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 62
    * Starting at 0x32a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1b5;
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
      assert s11.Peek(4) == 0x1b5;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 11, 0x139bdd08185b1b1bddd959);
      var s19 := Push1(s18, 0xaa);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(4) == 0x1b5;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s26, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b5;
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

  /** Node 51
    * Segment Id for this node is: 64
    * Starting at 0x364
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b5;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s52(s2, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 65
    * Starting at 0x366
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x366 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b5;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x045b);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s8, gas - 1)
      else
        ExecuteFromCFGNode_s53(s8, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 66
    * Starting at 0x370
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x370 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x1b5;
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x0382);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s9, gas - 1)
      else
        ExecuteFromCFGNode_s54(s9, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 67
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0382);
      assert s1.Peek(0) == 0x382;
      assert s1.Peek(6) == 0x1b5;
      var s2 := Push2(s1, 0x095d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s3, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 141
    * Starting at 0x95d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x382

    requires s0.stack[6] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x382;
      assert s1.Peek(6) == 0x1b5;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x382;
      assert s11.Peek(8) == 0x1b5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 56
    * Segment Id for this node is: 68
    * Starting at 0x382
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x382 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1b5;
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
      assert s11.Peek(5) == 0x1b5;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Dup2(s17);
      var s19 := And(s18);
      var s20 := Push0(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(8) == 0x1b5;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Dup1(s23);
      var s25 := Dup5(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x40);
      var s28 := Dup1(s27);
      var s29 := Dup3(s28);
      var s30 := Keccak256(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(9) == 0x1b5;
      var s32 := Dup2(s31);
      var s33 := MLoad(s32);
      var s34 := Dup1(s33);
      var s35 := Dup4(s34);
      var s36 := Add(s35);
      var s37 := Swap1(s36);
      var s38 := Swap3(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x05);
      var s41 := Dup3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s57(s41, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 69
    * Starting at 0x3b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(9) == 0x1b5;
      var s2 := PushN(s1, 5, 0x22a92927a9);
      var s3 := Push1(s2, 0xd9);
      var s4 := Shl(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Swap3(s8);
      var s10 := Dup3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(8) == 0x1b5;
      var s12 := Swap4(s11);
      var s13 := MStore(s12);
      var s14 := Swap1(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x03d4);
      var s19 := Swap1(s18);
      var s20 := Dup3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x3d4;
      assert s21.Peek(7) == 0x1b5;
      var s22 := Dup2(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0703);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s25, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 89
    * Starting at 0x703
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3d4

    requires s0.stack[8] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3d4;
      assert s1.Peek(8) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0726);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s9, gas - 1)
      else
        ExecuteFromCFGNode_s59(s9, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 90
    * Starting at 0x70e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x3d4

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x3d4;
      assert s1.Peek(11) == 0x1b5;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x035b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x35b;
      assert s11.Peek(7) == 0x3d4;
      assert s11.Peek(12) == 0x1b5;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0740);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s14, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 94
    * Starting at 0x740
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x740 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x35b

    requires s0.stack[7] == 0x3d4

    requires s0.stack[12] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x35b;
      assert s1.Peek(7) == 0x3d4;
      assert s1.Peek(12) == 0x1b5;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x3d4;
      assert s11.Peek(18) == 0x1b5;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s61(s14, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 95
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x3d4

    requires s0.stack[16] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x3d4;
      assert s1.Peek(16) == 0x1b5;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x076b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s7, gas - 1)
      else
        ExecuteFromCFGNode_s62(s7, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 96
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x3d4

    requires s0.stack[16] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x35b;
      assert s1.Peek(12) == 0x3d4;
      assert s1.Peek(17) == 0x1b5;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x3d4;
      assert s11.Peek(18) == 0x1b5;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x074f);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s16, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 97
    * Starting at 0x76b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x3d4

    requires s0.stack[16] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x3d4;
      assert s1.Peek(16) == 0x1b5;
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
      assert s11.Peek(7) == 0x35b;
      assert s11.Peek(12) == 0x3d4;
      assert s11.Peek(17) == 0x1b5;
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
      assert s21.Peek(5) == 0x35b;
      assert s21.Peek(10) == 0x3d4;
      assert s21.Peek(15) == 0x1b5;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s28, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x3d4

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3d4;
      assert s1.Peek(10) == 0x1b5;
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
    * Segment Id for this node is: 91
    * Starting at 0x726
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x3d4

    requires s0.stack[10] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3d4;
      assert s1.Peek(10) == 0x1b5;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s8, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 70
    * Starting at 0x3d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1b5;
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
      assert s11.Peek(8) == 0x1b5;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup2(s17);
      var s19 := Keccak256(s18);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x1b5;
      var s22 := Swap2(s21);
      var s23 := SStore(s22);
      var s24 := Dup1(s23);
      var s25 := MStore(s24);
      var s26 := Push32(s25, 0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5);
      var s27 := SLoad(s26);
      var s28 := Push2(s27, 0x041d);
      var s29 := Swap1(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x072e);
      assert s31.Peek(0) == 0x72e;
      assert s31.Peek(3) == 0x41d;
      assert s31.Peek(8) == 0x1b5;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s32, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 92
    * Starting at 0x72e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x41d

    requires s0.stack[7] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x41d;
      assert s1.Peek(7) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0739);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x099d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s7, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 146
    * Starting at 0x99d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x739

    requires s0.stack[6] == 0x41d

    requires s0.stack[11] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(6) == 0x41d;
      assert s1.Peek(11) == 0x1b5;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x028f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s10, gas - 1)
      else
        ExecuteFromCFGNode_s69(s10, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 147
    * Starting at 0x9a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x739

    requires s0.stack[7] == 0x41d

    requires s0.stack[12] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x028f);
      assert s1.Peek(0) == 0x28f;
      assert s1.Peek(4) == 0x739;
      assert s1.Peek(8) == 0x41d;
      assert s1.Peek(13) == 0x1b5;
      var s2 := Push2(s1, 0x0971);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s3, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 142
    * Starting at 0x971
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x971 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x28f

    requires s0.stack[4] == 0x739

    requires s0.stack[8] == 0x41d

    requires s0.stack[13] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x28f;
      assert s1.Peek(4) == 0x739;
      assert s1.Peek(8) == 0x41d;
      assert s1.Peek(13) == 0x1b5;
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
      assert s11.Peek(2) == 0x28f;
      assert s11.Peek(6) == 0x739;
      assert s11.Peek(10) == 0x41d;
      assert s11.Peek(15) == 0x1b5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 71
    * Segment Id for this node is: 53
    * Starting at 0x28f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x739

    requires s0.stack[7] == 0x41d

    requires s0.stack[12] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(7) == 0x41d;
      assert s1.Peek(12) == 0x1b5;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s6, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 93
    * Starting at 0x739
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x41d

    requires s0.stack[9] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x41d;
      assert s1.Peek(9) == 0x1b5;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s7, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 71
    * Starting at 0x41d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1b5;
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
      assert s11.Peek(4) == 0x1b5;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0453);
      var s15 := Dup2(s14);
      var s16 := Push2(s15, 0x0985);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s17, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 143
    * Starting at 0x985
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x985 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x453

    requires s0.stack[5] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x453;
      assert s1.Peek(5) == 0x1b5;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x0996);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s7, gas - 1)
      else
        ExecuteFromCFGNode_s75(s7, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 144
    * Starting at 0x98f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x453

    requires s0.stack[6] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0996);
      assert s1.Peek(0) == 0x996;
      assert s1.Peek(3) == 0x453;
      assert s1.Peek(7) == 0x1b5;
      var s2 := Push2(s1, 0x0971);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s3, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 142
    * Starting at 0x971
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x971 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x996

    requires s0.stack[3] == 0x453

    requires s0.stack[7] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x996;
      assert s1.Peek(3) == 0x453;
      assert s1.Peek(7) == 0x1b5;
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
      assert s11.Peek(2) == 0x996;
      assert s11.Peek(5) == 0x453;
      assert s11.Peek(9) == 0x1b5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 77
    * Segment Id for this node is: 145
    * Starting at 0x996
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x996 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x453

    requires s0.stack[6] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x453;
      assert s1.Peek(6) == 0x1b5;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s6, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 72
    * Starting at 0x453
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x453 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b5;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x0366);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 73
    * Starting at 0x45b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b5;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s4, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 39
    * Starting at 0x1b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b5 as nat
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

  /** Node 81
    * Segment Id for this node is: 35
    * Starting at 0x177
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x018a);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0x18a;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s13, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 36
    * Starting at 0x18a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18a;
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
      assert s11.Peek(2) == 0x18a;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x00ce);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s17, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 21
    * Starting at 0xce
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18a;
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

  /** Node 84
    * Segment Id for this node is: 9
    * Starting at 0x58
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x70a08231);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0134);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s6, gas - 1)
      else
        ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 10
    * Starting at 0x64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x015c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s5, gas - 1)
      else
        ExecuteFromCFGNode_s86(s5, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 11
    * Starting at 0x6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0164);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s5, gas - 1)
      else
        ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 12
    * Starting at 0x7a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
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

  /** Node 88
    * Segment Id for this node is: 33
    * Starting at 0x164
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x164 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ea);
      var s3 := Push2(s2, 0x0172);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x07a6);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s7, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 101
    * Starting at 0x7a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x172

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x172;
      assert s1.Peek(3) == 0xea;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x07b7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s11, gas - 1)
      else
        ExecuteFromCFGNode_s90(s11, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 102
    * Starting at 0x7b4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x172

    requires s0.stack[5] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x172;
      assert s1.Peek(6) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 91
    * Segment Id for this node is: 103
    * Starting at 0x7b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x172

    requires s0.stack[5] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x172;
      assert s1.Peek(5) == 0xea;
      var s2 := Push2(s1, 0x07c0);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x078b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s5, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x7c0

    requires s0.stack[6] == 0x172

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7c0;
      assert s1.Peek(6) == 0x172;
      assert s1.Peek(7) == 0xea;
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
      assert s11.Peek(4) == 0x7c0;
      assert s11.Peek(9) == 0x172;
      assert s11.Peek(10) == 0xea;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s14, gas - 1)
      else
        ExecuteFromCFGNode_s93(s14, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x7c0

    requires s0.stack[7] == 0x172

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x7c0;
      assert s1.Peek(8) == 0x172;
      assert s1.Peek(9) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 94
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x7c0

    requires s0.stack[7] == 0x172

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7c0;
      assert s1.Peek(7) == 0x172;
      assert s1.Peek(8) == 0xea;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s5, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 104
    * Starting at 0x7c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x172

    requires s0.stack[6] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x172;
      assert s1.Peek(6) == 0xea;
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
      assert s11.Peek(1) == 0x172;
      assert s11.Peek(4) == 0xea;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s13, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 34
    * Starting at 0x172
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x172 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push2(s1, 0x030b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s3, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 60
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x028b);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0583);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s8, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 81
    * Starting at 0x583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(7) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x05e7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s10, gas - 1)
      else
        ExecuteFromCFGNode_s99(s10, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 82
    * Starting at 0x592
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x592 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(6) == 0x28b;
      assert s11.Peek(10) == 0xea;
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
      assert s21.Peek(6) == 0x28b;
      assert s21.Peek(10) == 0xea;
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
      assert s31.Peek(4) == 0x28b;
      assert s31.Peek(8) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s33, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x28b

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
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

  /** Node 101
    * Segment Id for this node is: 83
    * Starting at 0x5e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(7) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0649);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s10, gas - 1)
      else
        ExecuteFromCFGNode_s102(s10, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 84
    * Starting at 0x5f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(6) == 0x28b;
      assert s11.Peek(10) == 0xea;
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
      assert s21.Peek(6) == 0x28b;
      assert s21.Peek(10) == 0xea;
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
      assert s31.Peek(4) == 0x28b;
      assert s31.Peek(8) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s33, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 85
    * Starting at 0x649
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x649 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(7) == 0xea;
      var s2 := Push2(s1, 0x0685);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(3) == 0x685;
      assert s11.Peek(7) == 0x28b;
      assert s11.Peek(11) == 0xea;
      var s12 := Push1(s11, 0x26);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x09b1);
      var s18 := Push1(s17, 0x26);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(3) == 0x685;
      assert s21.Peek(7) == 0x28b;
      assert s21.Peek(11) == 0xea;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0xa0);
      var s24 := Shl(s23);
      var s25 := Sub(s24);
      var s26 := Dup7(s25);
      var s27 := And(s26);
      var s28 := Push0(s27);
      var s29 := Swap1(s28);
      var s30 := Dup2(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x685;
      assert s31.Peek(7) == 0x28b;
      assert s31.Peek(11) == 0xea;
      var s32 := Push1(s31, 0x20);
      var s33 := Dup2(s32);
      var s34 := Swap1(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := Swap1(s36);
      var s38 := Keccak256(s37);
      var s39 := SLoad(s38);
      var s40 := Swap2(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s104(s41, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 86
    * Starting at 0x681
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x681 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x685

    requires s0.stack[7] == 0x28b

    requires s0.stack[11] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0703);
      assert s1.Peek(0) == 0x703;
      assert s1.Peek(4) == 0x685;
      assert s1.Peek(8) == 0x28b;
      assert s1.Peek(12) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s2, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 89
    * Starting at 0x703
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x685

    requires s0.stack[7] == 0x28b

    requires s0.stack[11] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x685;
      assert s1.Peek(7) == 0x28b;
      assert s1.Peek(11) == 0xea;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0726);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s9, gas - 1)
      else
        ExecuteFromCFGNode_s106(s9, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 90
    * Starting at 0x70e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x685

    requires s0.stack[9] == 0x28b

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x685;
      assert s1.Peek(10) == 0x28b;
      assert s1.Peek(14) == 0xea;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x035b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x35b;
      assert s11.Peek(7) == 0x685;
      assert s11.Peek(11) == 0x28b;
      assert s11.Peek(15) == 0xea;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0740);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s14, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 94
    * Starting at 0x740
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x740 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x35b

    requires s0.stack[7] == 0x685

    requires s0.stack[11] == 0x28b

    requires s0.stack[15] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x35b;
      assert s1.Peek(7) == 0x685;
      assert s1.Peek(11) == 0x28b;
      assert s1.Peek(15) == 0xea;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x685;
      assert s11.Peek(17) == 0x28b;
      assert s11.Peek(21) == 0xea;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s108(s14, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 95
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x685

    requires s0.stack[15] == 0x28b

    requires s0.stack[19] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x685;
      assert s1.Peek(15) == 0x28b;
      assert s1.Peek(19) == 0xea;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x076b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s7, gas - 1)
      else
        ExecuteFromCFGNode_s109(s7, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 96
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x685

    requires s0.stack[15] == 0x28b

    requires s0.stack[19] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x35b;
      assert s1.Peek(12) == 0x685;
      assert s1.Peek(16) == 0x28b;
      assert s1.Peek(20) == 0xea;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x685;
      assert s11.Peek(17) == 0x28b;
      assert s11.Peek(21) == 0xea;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x074f);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s16, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 97
    * Starting at 0x76b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x685

    requires s0.stack[15] == 0x28b

    requires s0.stack[19] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x685;
      assert s1.Peek(15) == 0x28b;
      assert s1.Peek(19) == 0xea;
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
      assert s11.Peek(7) == 0x35b;
      assert s11.Peek(12) == 0x685;
      assert s11.Peek(16) == 0x28b;
      assert s11.Peek(20) == 0xea;
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
      assert s21.Peek(5) == 0x35b;
      assert s21.Peek(10) == 0x685;
      assert s21.Peek(14) == 0x28b;
      assert s21.Peek(18) == 0xea;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s28, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x685

    requires s0.stack[9] == 0x28b

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x685;
      assert s1.Peek(9) == 0x28b;
      assert s1.Peek(13) == 0xea;
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

  /** Node 112
    * Segment Id for this node is: 91
    * Starting at 0x726
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x685

    requires s0.stack[9] == 0x28b

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x685;
      assert s1.Peek(9) == 0x28b;
      assert s1.Peek(13) == 0xea;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s8, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 87
    * Starting at 0x685
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x28b

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x28b;
      assert s11.Peek(11) == 0xea;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x28b;
      assert s21.Peek(12) == 0xea;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup5(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(4) == 0x28b;
      assert s31.Peek(8) == 0xea;
      var s32 := SLoad(s31);
      var s33 := Push2(s32, 0x06b3);
      var s34 := Swap1(s33);
      var s35 := Dup3(s34);
      var s36 := Push2(s35, 0x072e);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s37, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 92
    * Starting at 0x72e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x6b3

    requires s0.stack[6] == 0x28b

    requires s0.stack[10] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6b3;
      assert s1.Peek(6) == 0x28b;
      assert s1.Peek(10) == 0xea;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0739);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x099d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s7, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 146
    * Starting at 0x99d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x739

    requires s0.stack[6] == 0x6b3

    requires s0.stack[10] == 0x28b

    requires s0.stack[14] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(6) == 0x6b3;
      assert s1.Peek(10) == 0x28b;
      assert s1.Peek(14) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x028f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s10, gas - 1)
      else
        ExecuteFromCFGNode_s116(s10, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 147
    * Starting at 0x9a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x739

    requires s0.stack[7] == 0x6b3

    requires s0.stack[11] == 0x28b

    requires s0.stack[15] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x028f);
      assert s1.Peek(0) == 0x28f;
      assert s1.Peek(4) == 0x739;
      assert s1.Peek(8) == 0x6b3;
      assert s1.Peek(12) == 0x28b;
      assert s1.Peek(16) == 0xea;
      var s2 := Push2(s1, 0x0971);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s3, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 142
    * Starting at 0x971
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x971 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x28f

    requires s0.stack[4] == 0x739

    requires s0.stack[8] == 0x6b3

    requires s0.stack[12] == 0x28b

    requires s0.stack[16] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x28f;
      assert s1.Peek(4) == 0x739;
      assert s1.Peek(8) == 0x6b3;
      assert s1.Peek(12) == 0x28b;
      assert s1.Peek(16) == 0xea;
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
      assert s11.Peek(2) == 0x28f;
      assert s11.Peek(6) == 0x739;
      assert s11.Peek(10) == 0x6b3;
      assert s11.Peek(14) == 0x28b;
      assert s11.Peek(18) == 0xea;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 118
    * Segment Id for this node is: 53
    * Starting at 0x28f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x739

    requires s0.stack[7] == 0x6b3

    requires s0.stack[11] == 0x28b

    requires s0.stack[15] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(7) == 0x6b3;
      assert s1.Peek(11) == 0x28b;
      assert s1.Peek(15) == 0xea;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s6, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 93
    * Starting at 0x739
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x6b3

    requires s0.stack[8] == 0x28b

    requires s0.stack[12] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b3;
      assert s1.Peek(8) == 0x28b;
      assert s1.Peek(12) == 0xea;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s7, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 88
    * Starting at 0x6b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x28b

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(8) == 0x28b;
      assert s11.Peek(12) == 0xea;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap2(s18);
      var s20 := Dup3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(10) == 0x28b;
      assert s21.Peek(14) == 0xea;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Swap1(s23);
      var s25 := Swap5(s24);
      var s26 := SStore(s25);
      var s27 := MLoad(s26);
      var s28 := Dup5(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x28b;
      assert s31.Peek(11) == 0xea;
      var s32 := Swap3(s31);
      var s33 := Swap2(s32);
      var s34 := Dup7(s33);
      var s35 := And(s34);
      var s36 := Swap2(s35);
      var s37 := Push32(s36, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s38 := Swap2(s37);
      var s39 := Add(s38);
      var s40 := Push2(s39, 0x0576);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s41, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 80
    * Starting at 0x576
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x576 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x28b

    requires s0.stack[11] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x28b;
      assert s1.Peek(11) == 0xea;
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
      assert s11.Peek(0) == 0x28b;
      assert s11.Peek(4) == 0xea;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s12, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 52
    * Starting at 0x28b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s123(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 53
    * Starting at 0x28f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 24
    * Starting at 0xea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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
      var s11 := Push2(s10, 0x00ce);
      assert s11.Peek(0) == 0xce;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s12, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 32
    * Starting at 0x15c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00c1);
      var s3 := Push2(s2, 0x02fc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s4, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 59
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc1;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x01fe);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0925);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s9, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 136
    * Starting at 0x925
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x925 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x1fe

    requires s0.stack[4] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1fe;
      assert s1.Peek(4) == 0xc1;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x0939);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s11, gas - 1)
      else
        ExecuteFromCFGNode_s128(s11, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 137
    * Starting at 0x933
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x933 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1fe

    requires s0.stack[6] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x1fe;
      assert s1.Peek(7) == 0xc1;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s129(s5, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 138
    * Starting at 0x939
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x939 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1fe

    requires s0.stack[6] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1fe;
      assert s1.Peek(6) == 0xc1;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0957);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s8, gas - 1)
      else
        ExecuteFromCFGNode_s130(s8, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 139
    * Starting at 0x944
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x944 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1fe

    requires s0.stack[6] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x1fe;
      assert s1.Peek(7) == 0xc1;
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

  /** Node 131
    * Segment Id for this node is: 140
    * Starting at 0x957
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x957 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1fe

    requires s0.stack[6] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1fe;
      assert s1.Peek(6) == 0xc1;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s6, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 43
    * Starting at 0x1fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc1;
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
      assert s11.Peek(4) == 0xc1;
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
      assert s21.Peek(5) == 0xc1;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x022a);
      assert s31.Peek(0) == 0x22a;
      assert s31.Peek(8) == 0xc1;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0925);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s34, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 136
    * Starting at 0x925
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x925 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x22a

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x22a;
      assert s1.Peek(8) == 0xc1;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x0939);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s11, gas - 1)
      else
        ExecuteFromCFGNode_s134(s11, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 137
    * Starting at 0x933
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x933 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x22a

    requires s0.stack[10] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x22a;
      assert s1.Peek(11) == 0xc1;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 138
    * Starting at 0x939
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x939 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x22a

    requires s0.stack[10] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22a;
      assert s1.Peek(10) == 0xc1;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0957);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s8, gas - 1)
      else
        ExecuteFromCFGNode_s136(s8, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 139
    * Starting at 0x944
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x944 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x22a

    requires s0.stack[10] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x22a;
      assert s1.Peek(11) == 0xc1;
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

  /** Node 137
    * Segment Id for this node is: 140
    * Starting at 0x957
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x957 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x22a

    requires s0.stack[10] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22a;
      assert s1.Peek(10) == 0xc1;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s6, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 44
    * Starting at 0x22a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc1;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0275);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s5, gas - 1)
      else
        ExecuteFromCFGNode_s139(s5, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 45
    * Starting at 0x231
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x231 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xc1;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x024c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s5, gas - 1)
      else
        ExecuteFromCFGNode_s140(s5, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 46
    * Starting at 0x239
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x239 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0xc1;
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
      assert s11.Peek(7) == 0xc1;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0275);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s14, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 50
    * Starting at 0x275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc1;
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
      ExecuteFromCFGNode_s142(s10, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 20
    * Starting at 0xc1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00ce);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0740);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s8, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 94
    * Starting at 0x740
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x740 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xce;
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
      assert s11.Peek(8) == 0xce;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s144(s14, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 95
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xce;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x076b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s7, gas - 1)
      else
        ExecuteFromCFGNode_s145(s7, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 96
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0xce;
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
      assert s11.Peek(8) == 0xce;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x074f);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s16, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 97
    * Starting at 0x76b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xce;
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
      assert s11.Peek(7) == 0xce;
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
      assert s21.Peek(5) == 0xce;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s28, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 47
    * Starting at 0x24c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc1;
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
      ExecuteFromCFGNode_s148(s11, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 48
    * Starting at 0x258
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x258 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xc1;
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
      assert s11.Peek(7) == 0xc1;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x0258);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s16, gas - 1)
      else
        ExecuteFromCFGNode_s149(s16, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 49
    * Starting at 0x26c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0xc1;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s141(s8, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 30
    * Starting at 0x134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00fe);
      var s3 := Push2(s2, 0x0142);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0807);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s7, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 110
    * Starting at 0x807
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x142

    requires s0.stack[3] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x142;
      assert s1.Peek(3) == 0xfe;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0817);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s10, gas - 1)
      else
        ExecuteFromCFGNode_s152(s10, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 111
    * Starting at 0x814
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x814 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x142

    requires s0.stack[4] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x142;
      assert s1.Peek(5) == 0xfe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 153
    * Segment Id for this node is: 112
    * Starting at 0x817
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x817 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x142

    requires s0.stack[4] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x142;
      assert s1.Peek(4) == 0xfe;
      var s2 := Push2(s1, 0x0739);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x078b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s5, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x739

    requires s0.stack[5] == 0x142

    requires s0.stack[6] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x739;
      assert s1.Peek(5) == 0x142;
      assert s1.Peek(6) == 0xfe;
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
      assert s11.Peek(4) == 0x739;
      assert s11.Peek(8) == 0x142;
      assert s11.Peek(9) == 0xfe;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s14, gas - 1)
      else
        ExecuteFromCFGNode_s155(s14, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x739

    requires s0.stack[6] == 0x142

    requires s0.stack[7] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(7) == 0x142;
      assert s1.Peek(8) == 0xfe;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 156
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x739

    requires s0.stack[6] == 0x142

    requires s0.stack[7] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(6) == 0x142;
      assert s1.Peek(7) == 0xfe;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s5, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 93
    * Starting at 0x739
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x142

    requires s0.stack[5] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x142;
      assert s1.Peek(5) == 0xfe;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s7, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 31
    * Starting at 0x142
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x142 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xfe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfe;
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
      assert s11.Peek(1) == 0xfe;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s21, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 13
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x06fdde03);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00b9);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s6, gas - 1)
      else
        ExecuteFromCFGNode_s160(s6, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 14
    * Starting at 0x89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x00d7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s5, gas - 1)
      else
        ExecuteFromCFGNode_s161(s5, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 15
    * Starting at 0x94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x00fa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s5, gas - 1)
      else
        ExecuteFromCFGNode_s162(s5, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 16
    * Starting at 0x9f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
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
      var s4 := Push2(s3, 0x010c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s5, gas - 1)
      else
        ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 17
    * Starting at 0xaa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x011f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s5, gas - 1)
      else
        ExecuteFromCFGNode_s164(s5, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 18
    * Starting at 0xb5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
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

  /** Node 165
    * Segment Id for this node is: 29
    * Starting at 0x11f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f as nat
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
      var s14 := Push2(s13, 0x00ce);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s15, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 27
    * Starting at 0x10c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ea);
      var s3 := Push2(s2, 0x011a);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x07ce);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s7, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 105
    * Starting at 0x7ce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x11a

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11a;
      assert s1.Peek(3) == 0xea;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x07e0);
      assert s11.Peek(0) == 0x7e0;
      assert s11.Peek(7) == 0x11a;
      assert s11.Peek(8) == 0xea;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s12, gas - 1)
      else
        ExecuteFromCFGNode_s168(s12, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 106
    * Starting at 0x7dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x11a

    requires s0.stack[6] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x11a;
      assert s1.Peek(7) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 169
    * Segment Id for this node is: 107
    * Starting at 0x7e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x11a

    requires s0.stack[6] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11a;
      assert s1.Peek(6) == 0xea;
      var s2 := Push2(s1, 0x07e9);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x078b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s5, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x7e9

    requires s0.stack[7] == 0x11a

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7e9;
      assert s1.Peek(7) == 0x11a;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(4) == 0x7e9;
      assert s11.Peek(10) == 0x11a;
      assert s11.Peek(11) == 0xea;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s14, gas - 1)
      else
        ExecuteFromCFGNode_s171(s14, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x7e9

    requires s0.stack[8] == 0x11a

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x7e9;
      assert s1.Peek(9) == 0x11a;
      assert s1.Peek(10) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 172
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x7e9

    requires s0.stack[8] == 0x11a

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7e9;
      assert s1.Peek(8) == 0x11a;
      assert s1.Peek(9) == 0xea;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 108
    * Starting at 0x7e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x11a

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x11a;
      assert s1.Peek(7) == 0xea;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x07f7);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x078b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s9, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x7f7

    requires s0.stack[7] == 0x11a

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7f7;
      assert s1.Peek(7) == 0x11a;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(4) == 0x7f7;
      assert s11.Peek(10) == 0x11a;
      assert s11.Peek(11) == 0xea;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s14, gas - 1)
      else
        ExecuteFromCFGNode_s175(s14, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x7f7

    requires s0.stack[8] == 0x11a

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x7f7;
      assert s1.Peek(9) == 0x11a;
      assert s1.Peek(10) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 176
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x7f7

    requires s0.stack[8] == 0x11a

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7f7;
      assert s1.Peek(8) == 0x11a;
      assert s1.Peek(9) == 0xea;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s5, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 109
    * Starting at 0x7f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x11a

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x11a;
      assert s1.Peek(7) == 0xea;
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
      assert s11.Peek(4) == 0x11a;
      assert s11.Peek(5) == 0xea;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s15, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 28
    * Starting at 0x11a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea;
      var s2 := Push2(s1, 0x0295);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s3, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 54
    * Starting at 0x295
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x295 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xea;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02a1);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0583);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s8, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 81
    * Starting at 0x583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2a1

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a1;
      assert s1.Peek(8) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x05e7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s10, gas - 1)
      else
        ExecuteFromCFGNode_s181(s10, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 82
    * Starting at 0x592
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x592 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2a1

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2a1;
      assert s1.Peek(9) == 0xea;
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
      assert s11.Peek(6) == 0x2a1;
      assert s11.Peek(11) == 0xea;
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
      assert s21.Peek(6) == 0x2a1;
      assert s21.Peek(11) == 0xea;
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
      assert s31.Peek(4) == 0x2a1;
      assert s31.Peek(9) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s33, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x2a1

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2a1;
      assert s1.Peek(9) == 0xea;
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
    * Segment Id for this node is: 83
    * Starting at 0x5e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2a1

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a1;
      assert s1.Peek(8) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0649);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s10, gas - 1)
      else
        ExecuteFromCFGNode_s184(s10, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 84
    * Starting at 0x5f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2a1

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2a1;
      assert s1.Peek(9) == 0xea;
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
      assert s11.Peek(6) == 0x2a1;
      assert s11.Peek(11) == 0xea;
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
      assert s21.Peek(6) == 0x2a1;
      assert s21.Peek(11) == 0xea;
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
      assert s31.Peek(4) == 0x2a1;
      assert s31.Peek(9) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s33, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 85
    * Starting at 0x649
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x649 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2a1

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a1;
      assert s1.Peek(8) == 0xea;
      var s2 := Push2(s1, 0x0685);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(3) == 0x685;
      assert s11.Peek(7) == 0x2a1;
      assert s11.Peek(12) == 0xea;
      var s12 := Push1(s11, 0x26);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x09b1);
      var s18 := Push1(s17, 0x26);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(3) == 0x685;
      assert s21.Peek(7) == 0x2a1;
      assert s21.Peek(12) == 0xea;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0xa0);
      var s24 := Shl(s23);
      var s25 := Sub(s24);
      var s26 := Dup7(s25);
      var s27 := And(s26);
      var s28 := Push0(s27);
      var s29 := Swap1(s28);
      var s30 := Dup2(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x685;
      assert s31.Peek(7) == 0x2a1;
      assert s31.Peek(12) == 0xea;
      var s32 := Push1(s31, 0x20);
      var s33 := Dup2(s32);
      var s34 := Swap1(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := Swap1(s36);
      var s38 := Keccak256(s37);
      var s39 := SLoad(s38);
      var s40 := Swap2(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s186(s41, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 86
    * Starting at 0x681
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x681 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x685

    requires s0.stack[7] == 0x2a1

    requires s0.stack[12] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0703);
      assert s1.Peek(0) == 0x703;
      assert s1.Peek(4) == 0x685;
      assert s1.Peek(8) == 0x2a1;
      assert s1.Peek(13) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s2, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 89
    * Starting at 0x703
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x685

    requires s0.stack[7] == 0x2a1

    requires s0.stack[12] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x685;
      assert s1.Peek(7) == 0x2a1;
      assert s1.Peek(12) == 0xea;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0726);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s9, gas - 1)
      else
        ExecuteFromCFGNode_s188(s9, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 90
    * Starting at 0x70e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x685

    requires s0.stack[9] == 0x2a1

    requires s0.stack[14] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x685;
      assert s1.Peek(10) == 0x2a1;
      assert s1.Peek(15) == 0xea;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x035b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x35b;
      assert s11.Peek(7) == 0x685;
      assert s11.Peek(11) == 0x2a1;
      assert s11.Peek(16) == 0xea;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0740);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s14, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 94
    * Starting at 0x740
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x740 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x35b

    requires s0.stack[7] == 0x685

    requires s0.stack[11] == 0x2a1

    requires s0.stack[16] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x35b;
      assert s1.Peek(7) == 0x685;
      assert s1.Peek(11) == 0x2a1;
      assert s1.Peek(16) == 0xea;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x685;
      assert s11.Peek(17) == 0x2a1;
      assert s11.Peek(22) == 0xea;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s190(s14, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 95
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x685

    requires s0.stack[15] == 0x2a1

    requires s0.stack[20] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x685;
      assert s1.Peek(15) == 0x2a1;
      assert s1.Peek(20) == 0xea;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x076b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s7, gas - 1)
      else
        ExecuteFromCFGNode_s191(s7, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 96
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x685

    requires s0.stack[15] == 0x2a1

    requires s0.stack[20] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x35b;
      assert s1.Peek(12) == 0x685;
      assert s1.Peek(16) == 0x2a1;
      assert s1.Peek(21) == 0xea;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x685;
      assert s11.Peek(17) == 0x2a1;
      assert s11.Peek(22) == 0xea;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x074f);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s16, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 97
    * Starting at 0x76b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x685

    requires s0.stack[15] == 0x2a1

    requires s0.stack[20] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x685;
      assert s1.Peek(15) == 0x2a1;
      assert s1.Peek(20) == 0xea;
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
      assert s11.Peek(7) == 0x35b;
      assert s11.Peek(12) == 0x685;
      assert s11.Peek(16) == 0x2a1;
      assert s11.Peek(21) == 0xea;
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
      assert s21.Peek(5) == 0x35b;
      assert s21.Peek(10) == 0x685;
      assert s21.Peek(14) == 0x2a1;
      assert s21.Peek(19) == 0xea;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s28, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x685

    requires s0.stack[9] == 0x2a1

    requires s0.stack[14] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x685;
      assert s1.Peek(9) == 0x2a1;
      assert s1.Peek(14) == 0xea;
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

  /** Node 194
    * Segment Id for this node is: 91
    * Starting at 0x726
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x685

    requires s0.stack[9] == 0x2a1

    requires s0.stack[14] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x685;
      assert s1.Peek(9) == 0x2a1;
      assert s1.Peek(14) == 0xea;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s8, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 87
    * Starting at 0x685
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x2a1

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2a1;
      assert s1.Peek(9) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x2a1;
      assert s11.Peek(12) == 0xea;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x2a1;
      assert s21.Peek(13) == 0xea;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap1(s25);
      var s27 := Dup5(s26);
      var s28 := And(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Keccak256(s30);
      assert s31.Peek(4) == 0x2a1;
      assert s31.Peek(9) == 0xea;
      var s32 := SLoad(s31);
      var s33 := Push2(s32, 0x06b3);
      var s34 := Swap1(s33);
      var s35 := Dup3(s34);
      var s36 := Push2(s35, 0x072e);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s37, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 92
    * Starting at 0x72e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x6b3

    requires s0.stack[6] == 0x2a1

    requires s0.stack[11] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6b3;
      assert s1.Peek(6) == 0x2a1;
      assert s1.Peek(11) == 0xea;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0739);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x099d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s7, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 146
    * Starting at 0x99d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x739

    requires s0.stack[6] == 0x6b3

    requires s0.stack[10] == 0x2a1

    requires s0.stack[15] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x739;
      assert s1.Peek(6) == 0x6b3;
      assert s1.Peek(10) == 0x2a1;
      assert s1.Peek(15) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x028f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s10, gas - 1)
      else
        ExecuteFromCFGNode_s198(s10, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 147
    * Starting at 0x9a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x739

    requires s0.stack[7] == 0x6b3

    requires s0.stack[11] == 0x2a1

    requires s0.stack[16] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x028f);
      assert s1.Peek(0) == 0x28f;
      assert s1.Peek(4) == 0x739;
      assert s1.Peek(8) == 0x6b3;
      assert s1.Peek(12) == 0x2a1;
      assert s1.Peek(17) == 0xea;
      var s2 := Push2(s1, 0x0971);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s3, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 142
    * Starting at 0x971
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x971 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x28f

    requires s0.stack[4] == 0x739

    requires s0.stack[8] == 0x6b3

    requires s0.stack[12] == 0x2a1

    requires s0.stack[17] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x28f;
      assert s1.Peek(4) == 0x739;
      assert s1.Peek(8) == 0x6b3;
      assert s1.Peek(12) == 0x2a1;
      assert s1.Peek(17) == 0xea;
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
      assert s11.Peek(2) == 0x28f;
      assert s11.Peek(6) == 0x739;
      assert s11.Peek(10) == 0x6b3;
      assert s11.Peek(14) == 0x2a1;
      assert s11.Peek(19) == 0xea;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 200
    * Segment Id for this node is: 53
    * Starting at 0x28f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x739

    requires s0.stack[7] == 0x6b3

    requires s0.stack[11] == 0x2a1

    requires s0.stack[16] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x739;
      assert s1.Peek(7) == 0x6b3;
      assert s1.Peek(11) == 0x2a1;
      assert s1.Peek(16) == 0xea;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s6, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 93
    * Starting at 0x739
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x6b3

    requires s0.stack[8] == 0x2a1

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6b3;
      assert s1.Peek(8) == 0x2a1;
      assert s1.Peek(13) == 0xea;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s7, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 88
    * Starting at 0x6b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x2a1

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2a1;
      assert s1.Peek(9) == 0xea;
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
      assert s11.Peek(8) == 0x2a1;
      assert s11.Peek(13) == 0xea;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Swap2(s18);
      var s20 := Dup3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(10) == 0x2a1;
      assert s21.Peek(15) == 0xea;
      var s22 := Keccak256(s21);
      var s23 := Swap5(s22);
      var s24 := Swap1(s23);
      var s25 := Swap5(s24);
      var s26 := SStore(s25);
      var s27 := MLoad(s26);
      var s28 := Dup5(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x2a1;
      assert s31.Peek(12) == 0xea;
      var s32 := Swap3(s31);
      var s33 := Swap2(s32);
      var s34 := Dup7(s33);
      var s35 := And(s34);
      var s36 := Swap2(s35);
      var s37 := Push32(s36, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s38 := Swap2(s37);
      var s39 := Add(s38);
      var s40 := Push2(s39, 0x0576);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s41, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 80
    * Starting at 0x576
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x576 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x2a1

    requires s0.stack[12] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2a1;
      assert s1.Peek(12) == 0xea;
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
      assert s11.Peek(0) == 0x2a1;
      assert s11.Peek(5) == 0xea;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s12, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 55
    * Starting at 0x2a1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xea;
      var s2 := Push2(s1, 0x02f2);
      var s3 := Dup5(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x02ed);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x60);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x2ed;
      assert s11.Peek(6) == 0x2f2;
      assert s11.Peek(11) == 0xea;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := Push1(s14, 0x28);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x09d7);
      var s21 := Push1(s20, 0x28);
      assert s21.Peek(5) == 0x2ed;
      assert s21.Peek(8) == 0x2f2;
      assert s21.Peek(13) == 0xea;
      var s22 := Swap2(s21);
      var s23 := CodeCopy(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0xa0);
      var s27 := Shl(s26);
      var s28 := Sub(s27);
      var s29 := Dup11(s28);
      var s30 := And(s29);
      var s31 := Push0(s30);
      assert s31.Peek(4) == 0x2ed;
      assert s31.Peek(7) == 0x2f2;
      assert s31.Peek(12) == 0xea;
      var s32 := Swap1(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x01);
      var s36 := Push1(s35, 0x20);
      var s37 := Swap1(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x40);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s205(s41, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 56
    * Starting at 0x2dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x2ed

    requires s0.stack[9] == 0x2f2

    requires s0.stack[14] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x2ed;
      assert s1.Peek(10) == 0x2f2;
      assert s1.Peek(15) == 0xea;
      var s2 := Keccak256(s1);
      var s3 := Caller(s2);
      var s4 := Dup5(s3);
      var s5 := MStore(s4);
      var s6 := Swap1(s5);
      var s7 := Swap2(s6);
      var s8 := MStore(s7);
      var s9 := Swap1(s8);
      var s10 := Keccak256(s9);
      var s11 := SLoad(s10);
      assert s11.Peek(3) == 0x2ed;
      assert s11.Peek(6) == 0x2f2;
      assert s11.Peek(11) == 0xea;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0703);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s15, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 89
    * Starting at 0x703
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x2ed

    requires s0.stack[6] == 0x2f2

    requires s0.stack[11] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ed;
      assert s1.Peek(6) == 0x2f2;
      assert s1.Peek(11) == 0xea;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0726);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s9, gas - 1)
      else
        ExecuteFromCFGNode_s207(s9, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 90
    * Starting at 0x70e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x2ed

    requires s0.stack[8] == 0x2f2

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x2ed;
      assert s1.Peek(9) == 0x2f2;
      assert s1.Peek(14) == 0xea;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x035b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x35b;
      assert s11.Peek(7) == 0x2ed;
      assert s11.Peek(10) == 0x2f2;
      assert s11.Peek(15) == 0xea;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0740);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s14, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 94
    * Starting at 0x740
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x740 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x35b

    requires s0.stack[7] == 0x2ed

    requires s0.stack[10] == 0x2f2

    requires s0.stack[15] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x35b;
      assert s1.Peek(7) == 0x2ed;
      assert s1.Peek(10) == 0x2f2;
      assert s1.Peek(15) == 0xea;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x2ed;
      assert s11.Peek(16) == 0x2f2;
      assert s11.Peek(21) == 0xea;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s209(s14, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 95
    * Starting at 0x74f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x2ed

    requires s0.stack[14] == 0x2f2

    requires s0.stack[19] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x2ed;
      assert s1.Peek(14) == 0x2f2;
      assert s1.Peek(19) == 0xea;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x076b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s7, gas - 1)
      else
        ExecuteFromCFGNode_s210(s7, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 96
    * Starting at 0x758
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x758 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x2ed

    requires s0.stack[14] == 0x2f2

    requires s0.stack[19] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x35b;
      assert s1.Peek(12) == 0x2ed;
      assert s1.Peek(15) == 0x2f2;
      assert s1.Peek(20) == 0xea;
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
      assert s11.Peek(8) == 0x35b;
      assert s11.Peek(13) == 0x2ed;
      assert s11.Peek(16) == 0x2f2;
      assert s11.Peek(21) == 0xea;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x074f);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s16, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 97
    * Starting at 0x76b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x35b

    requires s0.stack[11] == 0x2ed

    requires s0.stack[14] == 0x2f2

    requires s0.stack[19] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x35b;
      assert s1.Peek(11) == 0x2ed;
      assert s1.Peek(14) == 0x2f2;
      assert s1.Peek(19) == 0xea;
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
      assert s11.Peek(7) == 0x35b;
      assert s11.Peek(12) == 0x2ed;
      assert s11.Peek(15) == 0x2f2;
      assert s11.Peek(20) == 0xea;
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
      assert s21.Peek(5) == 0x35b;
      assert s21.Peek(10) == 0x2ed;
      assert s21.Peek(13) == 0x2f2;
      assert s21.Peek(18) == 0xea;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s28, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x2ed

    requires s0.stack[8] == 0x2f2

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2ed;
      assert s1.Peek(8) == 0x2f2;
      assert s1.Peek(13) == 0xea;
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
    * Segment Id for this node is: 91
    * Starting at 0x726
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x726 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x2ed

    requires s0.stack[8] == 0x2f2

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2ed;
      assert s1.Peek(8) == 0x2f2;
      assert s1.Peek(13) == 0xea;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s8, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 57
    * Starting at 0x2ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2f2

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f2;
      assert s1.Peek(8) == 0xea;
      var s2 := Push2(s1, 0x045f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s3, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 74
    * Starting at 0x45f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2f2

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f2;
      assert s1.Peek(8) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x04c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s10, gas - 1)
      else
        ExecuteFromCFGNode_s216(s10, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 75
    * Starting at 0x46e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2f2

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2f2;
      assert s1.Peek(9) == 0xea;
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
      assert s11.Peek(6) == 0x2f2;
      assert s11.Peek(11) == 0xea;
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
      assert s21.Peek(6) == 0x2f2;
      assert s21.Peek(11) == 0xea;
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
      assert s31.Peek(4) == 0x2f2;
      assert s31.Peek(9) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s33, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 63
    * Starting at 0x35b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x2f2

    requires s0.stack[9] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2f2;
      assert s1.Peek(9) == 0xea;
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

  /** Node 218
    * Segment Id for this node is: 76
    * Starting at 0x4c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2f2

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f2;
      assert s1.Peek(8) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0522);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s10, gas - 1)
      else
        ExecuteFromCFGNode_s219(s10, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 77
    * Starting at 0x4d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2f2

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2f2;
      assert s1.Peek(9) == 0xea;
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
      assert s11.Peek(6) == 0x2f2;
      assert s11.Peek(11) == 0xea;
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
      assert s21.Peek(6) == 0x2f2;
      assert s21.Peek(11) == 0xea;
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
      assert s31.Peek(4) == 0x2f2;
      assert s31.Peek(9) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s33, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 78
    * Starting at 0x522
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x522 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2f2

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f2;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(7) == 0x2f2;
      assert s11.Peek(12) == 0xea;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x2f2;
      assert s21.Peek(15) == 0xea;
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
      assert s31.Peek(8) == 0x2f2;
      assert s31.Peek(13) == 0xea;
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
      ExecuteFromCFGNode_s221(s41, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 79
    * Starting at 0x551
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x2f2

    requires s0.stack[13] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x2f2;
      assert s1.Peek(14) == 0xea;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 80
    * Starting at 0x576
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x576 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x2f2

    requires s0.stack[12] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2f2;
      assert s1.Peek(12) == 0xea;
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
      assert s11.Peek(0) == 0x2f2;
      assert s11.Peek(5) == 0xea;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s12, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 58
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xea;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s9, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 25
    * Starting at 0xfa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
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

  /** Node 225
    * Segment Id for this node is: 22
    * Starting at 0xd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
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
      var s6 := Push2(s5, 0x07a6);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s7, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 101
    * Starting at 0x7a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a6 as nat
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
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x07b7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s11, gas - 1)
      else
        ExecuteFromCFGNode_s227(s11, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 102
    * Starting at 0x7b4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xe5

    requires s0.stack[5] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0xe5;
      assert s1.Peek(6) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 228
    * Segment Id for this node is: 103
    * Starting at 0x7b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xe5

    requires s0.stack[5] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe5;
      assert s1.Peek(5) == 0xea;
      var s2 := Push2(s1, 0x07c0);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x078b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s5, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 98
    * Starting at 0x78b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x7c0

    requires s0.stack[6] == 0xe5

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7c0;
      assert s1.Peek(6) == 0xe5;
      assert s1.Peek(7) == 0xea;
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
      assert s11.Peek(4) == 0x7c0;
      assert s11.Peek(9) == 0xe5;
      assert s11.Peek(10) == 0xea;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x07a1);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s14, gas - 1)
      else
        ExecuteFromCFGNode_s230(s14, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 99
    * Starting at 0x79e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x7c0

    requires s0.stack[7] == 0xe5

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0x7c0;
      assert s1.Peek(8) == 0xe5;
      assert s1.Peek(9) == 0xea;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 231
    * Segment Id for this node is: 100
    * Starting at 0x7a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x7c0

    requires s0.stack[7] == 0xe5

    requires s0.stack[8] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7c0;
      assert s1.Peek(7) == 0xe5;
      assert s1.Peek(8) == 0xea;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s5, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 104
    * Starting at 0x7c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xe5

    requires s0.stack[6] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe5;
      assert s1.Peek(6) == 0xea;
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
      assert s11.Peek(1) == 0xe5;
      assert s11.Peek(4) == 0xea;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s13, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 23
    * Starting at 0xe5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push2(s1, 0x027f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s3, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 51
    * Starting at 0x27f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xea;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x028b);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x045f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s8, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 74
    * Starting at 0x45f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(7) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x04c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s10, gas - 1)
      else
        ExecuteFromCFGNode_s236(s10, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 75
    * Starting at 0x46e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(6) == 0x28b;
      assert s11.Peek(10) == 0xea;
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
      assert s21.Peek(6) == 0x28b;
      assert s21.Peek(10) == 0xea;
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
      assert s31.Peek(4) == 0x28b;
      assert s31.Peek(8) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s33, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 76
    * Starting at 0x4c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(7) == 0xea;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0522);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s10, gas - 1)
      else
        ExecuteFromCFGNode_s238(s10, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 77
    * Starting at 0x4d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x28b;
      assert s1.Peek(8) == 0xea;
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
      assert s11.Peek(6) == 0x28b;
      assert s11.Peek(10) == 0xea;
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
      assert s21.Peek(6) == 0x28b;
      assert s21.Peek(10) == 0xea;
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
      assert s31.Peek(4) == 0x28b;
      assert s31.Peek(8) == 0xea;
      var s32 := Push2(s31, 0x035b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s33, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 78
    * Starting at 0x522
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x522 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x28b

    requires s0.stack[7] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x28b;
      assert s1.Peek(7) == 0xea;
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
      assert s11.Peek(7) == 0x28b;
      assert s11.Peek(11) == 0xea;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x28b;
      assert s21.Peek(14) == 0xea;
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
      assert s31.Peek(8) == 0x28b;
      assert s31.Peek(12) == 0xea;
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
      ExecuteFromCFGNode_s240(s41, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 79
    * Starting at 0x551
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x551 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x28b

    requires s0.stack[12] == 0xea

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x28b;
      assert s1.Peek(13) == 0xea;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s5, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 19
    * Starting at 0xb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00c1);
      var s3 := Push2(s2, 0x01ef);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s4, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 42
    * Starting at 0x1ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xc1;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x01fe);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0925);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s9, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 18
    * Starting at 0xb5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5 as nat
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
