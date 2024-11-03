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
      var s7 := Push2(s6, 0x0087);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s483(s8, gas - 1)
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
      var s1 := Push0(s0);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shr(s3);
      var s5 := Dup1(s4);
      var s6 := Push4(s5, 0x313ce567);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0057);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s9, gas - 1)
      else
        ExecuteFromCFGNode_s2(s9, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x1d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0439);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0464);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x33
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x048f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x04a3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x49
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x04c2);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s5, gas - 1)
      else
        ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x54
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54 as nat
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

  /** Node 8
    * Segment Id for this node is: 85
    * Starting at 0x4c2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c2 as nat
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
      var s5 := Push2(s4, 0x04cd);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 86
    * Starting at 0x4ca
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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
    * Segment Id for this node is: 87
    * Starting at 0x4cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x040c);
      var s4 := Push2(s3, 0x04dc);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0bff);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 198
    * Starting at 0xbff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x4dc

    requires s0.stack[3] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4dc;
      assert s1.Peek(3) == 0x40c;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0c10);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s11, gas - 1)
      else
        ExecuteFromCFGNode_s12(s11, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 199
    * Starting at 0xc0d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x4dc

    requires s0.stack[5] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x4dc;
      assert s1.Peek(6) == 0x40c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 13
    * Segment Id for this node is: 200
    * Starting at 0xc10
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x4dc

    requires s0.stack[5] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4dc;
      assert s1.Peek(5) == 0x40c;
      var s2 := Push2(s1, 0x0c19);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0b6a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s5, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xc19

    requires s0.stack[6] == 0x4dc

    requires s0.stack[7] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc19;
      assert s1.Peek(6) == 0x4dc;
      assert s1.Peek(7) == 0x40c;
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
      assert s11.Peek(4) == 0xc19;
      assert s11.Peek(9) == 0x4dc;
      assert s11.Peek(10) == 0x40c;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s14, gas - 1)
      else
        ExecuteFromCFGNode_s15(s14, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xc19

    requires s0.stack[7] == 0x4dc

    requires s0.stack[8] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xc19;
      assert s1.Peek(8) == 0x4dc;
      assert s1.Peek(9) == 0x40c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xc19

    requires s0.stack[7] == 0x4dc

    requires s0.stack[8] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc19;
      assert s1.Peek(7) == 0x4dc;
      assert s1.Peek(8) == 0x40c;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 201
    * Starting at 0xc19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x4dc

    requires s0.stack[6] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4dc;
      assert s1.Peek(6) == 0x40c;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0c27);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b6a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s9, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xc27

    requires s0.stack[6] == 0x4dc

    requires s0.stack[7] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc27;
      assert s1.Peek(6) == 0x4dc;
      assert s1.Peek(7) == 0x40c;
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
      assert s11.Peek(4) == 0xc27;
      assert s11.Peek(9) == 0x4dc;
      assert s11.Peek(10) == 0x40c;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s14, gas - 1)
      else
        ExecuteFromCFGNode_s19(s14, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xc27

    requires s0.stack[7] == 0x4dc

    requires s0.stack[8] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xc27;
      assert s1.Peek(8) == 0x4dc;
      assert s1.Peek(9) == 0x40c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 20
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xc27

    requires s0.stack[7] == 0x4dc

    requires s0.stack[8] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc27;
      assert s1.Peek(7) == 0x4dc;
      assert s1.Peek(8) == 0x40c;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s5, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 202
    * Starting at 0xc27
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x4dc

    requires s0.stack[6] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4dc;
      assert s1.Peek(6) == 0x40c;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s9, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 88
    * Starting at 0x4dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x40c;
      var s2 := Push1(s1, 0x03);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push0(s6);
      var s8 := Swap3(s7);
      var s9 := Dup4(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x40c;
      var s12 := Dup1(s11);
      var s13 := Dup5(s12);
      var s14 := Keccak256(s13);
      var s15 := Swap1(s14);
      var s16 := Swap2(s15);
      var s17 := MStore(s16);
      var s18 := Swap1(s17);
      var s19 := Dup3(s18);
      var s20 := MStore(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x40c;
      var s22 := Keccak256(s21);
      var s23 := SLoad(s22);
      var s24 := Dup2(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s25, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 65
    * Starting at 0x40c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x40c;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x03c0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 56
    * Starting at 0x3c0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x40c;
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

  /** Node 25
    * Segment Id for this node is: 81
    * Starting at 0x4a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a3 as nat
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
      var s5 := Push2(s4, 0x04ae);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s6, gas - 1)
      else
        ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 82
    * Starting at 0x4ab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 27
    * Segment Id for this node is: 83
    * Starting at 0x4ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x03e8);
      var s4 := Push2(s3, 0x04bd);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b85);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s8, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 186
    * Starting at 0xb85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x4bd

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4bd;
      assert s1.Peek(3) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b96);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s11, gas - 1)
      else
        ExecuteFromCFGNode_s29(s11, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 187
    * Starting at 0xb93
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x4bd

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x4bd;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 30
    * Segment Id for this node is: 188
    * Starting at 0xb96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x4bd

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4bd;
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x0b9f);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0b6a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s5, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb9f

    requires s0.stack[6] == 0x4bd

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb9f;
      assert s1.Peek(6) == 0x4bd;
      assert s1.Peek(7) == 0x3e8;
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
      assert s11.Peek(4) == 0xb9f;
      assert s11.Peek(9) == 0x4bd;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s14, gas - 1)
      else
        ExecuteFromCFGNode_s32(s14, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb9f

    requires s0.stack[7] == 0x4bd

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xb9f;
      assert s1.Peek(8) == 0x4bd;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb9f

    requires s0.stack[7] == 0x4bd

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb9f;
      assert s1.Peek(7) == 0x4bd;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 189
    * Starting at 0xb9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x4bd

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4bd;
      assert s1.Peek(6) == 0x3e8;
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
      assert s11.Peek(1) == 0x4bd;
      assert s11.Peek(4) == 0x3e8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s13, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 84
    * Starting at 0x4bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e8;
      var s2 := Push2(s1, 0x0926);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 137
    * Starting at 0x926
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x926 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e8;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x3e8;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0940);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s18, gas - 1)
      else
        ExecuteFromCFGNode_s37(s18, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 138
    * Starting at 0x93d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 38
    * Segment Id for this node is: 139
    * Starting at 0x940
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x940 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e8;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x3e8;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Dup5(s14);
      var s16 := Swap3(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x095e);
      var s19 := Swap1(s18);
      var s20 := Dup5(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x95e;
      assert s21.Peek(9) == 0x3e8;
      var s22 := Push2(s21, 0x09ec);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s23, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x95e

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x95e;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s10, gas - 1)
      else
        ExecuteFromCFGNode_s40(s10, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x95e

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x95e;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s3, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x95e

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x95e;
      assert s1.Peek(11) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x95e;
      assert s11.Peek(13) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 42
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x95e

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x95e;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s6, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 140
    * Starting at 0x95e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(4) == 0x3e8;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Push0(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x02);
      var s19 := Push1(s18, 0x20);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(5) == 0x3e8;
      var s22 := Dup2(s21);
      var s23 := Keccak256(s22);
      var s24 := Dup1(s23);
      var s25 := SLoad(s24);
      var s26 := Dup5(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x098a);
      var s30 := Swap1(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(2) == 0x98a;
      assert s31.Peek(9) == 0x3e8;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0b0b);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s34, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x98a

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x98a;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s10, gas - 1)
      else
        ExecuteFromCFGNode_s45(s10, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x98a

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x98a;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s3, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x98a

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x98a;
      assert s1.Peek(11) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x98a;
      assert s11.Peek(13) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 47
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x98a

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x98a;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 141
    * Starting at 0x98a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup3(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x3e8;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup5(s16);
      var s18 := And(s17);
      var s19 := Swap1(s18);
      var s20 := Caller(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(6) == 0x3e8;
      var s22 := Push0(s21);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Push2(s25, 0x0c89);
      var s27 := Dup4(s26);
      var s28 := CodeCopy(s27);
      var s29 := Dup2(s28);
      var s30 := MLoad(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(9) == 0x3e8;
      var s32 := MStore(s31);
      var s33 := Swap1(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push2(s35, 0x06c4);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s37, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 110
    * Starting at 0x6c4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s10, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 61
    * Starting at 0x3e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
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
      var s11 := Push2(s10, 0x03c0);
      assert s11.Peek(0) == 0x3c0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s12, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 56
    * Starting at 0x3c0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
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

  /** Node 53
    * Segment Id for this node is: 78
    * Starting at 0x48f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48f as nat
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
      var s5 := Push2(s4, 0x049a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s6, gas - 1)
      else
        ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 79
    * Starting at 0x497
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 55
    * Segment Id for this node is: 80
    * Starting at 0x49a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x03b3);
      var s4 := Push2(s3, 0x0919);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s5, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 136
    * Starting at 0x919
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x919 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3b3;
      var s2 := Push1(s1, 0x05);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0505);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0c30);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s8, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 203
    * Starting at 0xc30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x505

    requires s0.stack[3] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x505;
      assert s1.Peek(3) == 0x3b3;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x0c44);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s11, gas - 1)
      else
        ExecuteFromCFGNode_s58(s11, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 204
    * Starting at 0xc3e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x505

    requires s0.stack[5] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x505;
      assert s1.Peek(6) == 0x3b3;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s59(s5, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 205
    * Starting at 0xc44
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x505

    requires s0.stack[5] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x505;
      assert s1.Peek(5) == 0x3b3;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0c62);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s8, gas - 1)
      else
        ExecuteFromCFGNode_s60(s8, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 206
    * Starting at 0xc4f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x505

    requires s0.stack[5] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x505;
      assert s1.Peek(6) == 0x3b3;
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

  /** Node 61
    * Segment Id for this node is: 207
    * Starting at 0xc62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x505

    requires s0.stack[5] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x505;
      assert s1.Peek(5) == 0x3b3;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s6, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 90
    * Starting at 0x505
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x505 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3b3;
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
      assert s11.Peek(3) == 0x3b3;
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
      assert s21.Peek(4) == 0x3b3;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x0531);
      assert s31.Peek(0) == 0x531;
      assert s31.Peek(7) == 0x3b3;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0c30);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s34, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 203
    * Starting at 0xc30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x531

    requires s0.stack[7] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x531;
      assert s1.Peek(7) == 0x3b3;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x0c44);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s11, gas - 1)
      else
        ExecuteFromCFGNode_s64(s11, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 204
    * Starting at 0xc3e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x531

    requires s0.stack[9] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x531;
      assert s1.Peek(10) == 0x3b3;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s5, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 205
    * Starting at 0xc44
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x531

    requires s0.stack[9] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x531;
      assert s1.Peek(9) == 0x3b3;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0c62);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s8, gas - 1)
      else
        ExecuteFromCFGNode_s66(s8, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 206
    * Starting at 0xc4f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x531

    requires s0.stack[9] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x531;
      assert s1.Peek(10) == 0x3b3;
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

  /** Node 67
    * Segment Id for this node is: 207
    * Starting at 0xc62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x531

    requires s0.stack[9] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x531;
      assert s1.Peek(9) == 0x3b3;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s6, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 91
    * Starting at 0x531
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x531 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3b3;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x057c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s5, gas - 1)
      else
        ExecuteFromCFGNode_s69(s5, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 92
    * Starting at 0x538
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x538 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(7) == 0x3b3;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0553);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s5, gas - 1)
      else
        ExecuteFromCFGNode_s70(s5, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 93
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(7) == 0x3b3;
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
      assert s11.Peek(6) == 0x3b3;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x057c);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s14, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 97
    * Starting at 0x57c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3b3;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s8, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 55
    * Starting at 0x3b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b3;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x03c0);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0b1e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s8, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 179
    * Starting at 0xb1e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x3c0

    requires s0.stack[3] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c0;
      assert s1.Peek(3) == 0x3b3;
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
      assert s11.Peek(8) == 0x3c0;
      assert s11.Peek(9) == 0x3b3;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s74(s14, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 180
    * Starting at 0xb2e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x3c0

    requires s0.stack[7] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3c0;
      assert s1.Peek(7) == 0x3b3;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0b4a);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s7, gas - 1)
      else
        ExecuteFromCFGNode_s75(s7, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 181
    * Starting at 0xb37
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x3c0

    requires s0.stack[7] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3c0;
      assert s1.Peek(8) == 0x3b3;
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
      assert s11.Peek(8) == 0x3c0;
      assert s11.Peek(9) == 0x3b3;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0b2e);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s16, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 182
    * Starting at 0xb4a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x3c0

    requires s0.stack[7] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3c0;
      assert s1.Peek(7) == 0x3b3;
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
      assert s11.Peek(7) == 0x3c0;
      assert s11.Peek(8) == 0x3b3;
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
      assert s21.Peek(5) == 0x3c0;
      assert s21.Peek(6) == 0x3b3;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s28, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 56
    * Starting at 0x3c0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b3;
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

  /** Node 78
    * Segment Id for this node is: 94
    * Starting at 0x553
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x553 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3b3;
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
      ExecuteFromCFGNode_s79(s11, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 95
    * Starting at 0x55f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3b3;
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
      assert s11.Peek(6) == 0x3b3;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x055f);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s16, gas - 1)
      else
        ExecuteFromCFGNode_s80(s16, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 96
    * Starting at 0x573
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x573 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(7) == 0x3b3;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s71(s8, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 74
    * Starting at 0x464
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x464 as nat
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
      var s5 := Push2(s4, 0x046f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s6, gas - 1)
      else
        ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 75
    * Starting at 0x46c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 83
    * Segment Id for this node is: 76
    * Starting at 0x46f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x040c);
      var s4 := Push2(s3, 0x047e);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0be6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s8, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 195
    * Starting at 0xbe6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x47e

    requires s0.stack[3] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x47e;
      assert s1.Peek(3) == 0x40c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0bf6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s10, gas - 1)
      else
        ExecuteFromCFGNode_s85(s10, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 196
    * Starting at 0xbf3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x47e

    requires s0.stack[4] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x47e;
      assert s1.Peek(5) == 0x40c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 86
    * Segment Id for this node is: 197
    * Starting at 0xbf6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x47e

    requires s0.stack[4] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x47e;
      assert s1.Peek(4) == 0x40c;
      var s2 := Push2(s1, 0x0aed);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0b6a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xaed

    requires s0.stack[5] == 0x47e

    requires s0.stack[6] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xaed;
      assert s1.Peek(5) == 0x47e;
      assert s1.Peek(6) == 0x40c;
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
      assert s11.Peek(4) == 0xaed;
      assert s11.Peek(8) == 0x47e;
      assert s11.Peek(9) == 0x40c;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s14, gas - 1)
      else
        ExecuteFromCFGNode_s88(s14, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x47e

    requires s0.stack[7] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x47e;
      assert s1.Peek(8) == 0x40c;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 89
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x47e

    requires s0.stack[7] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x47e;
      assert s1.Peek(7) == 0x40c;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s5, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x47e

    requires s0.stack[5] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47e;
      assert s1.Peek(5) == 0x40c;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s7, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 77
    * Starting at 0x47e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x40c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x40c;
      var s2 := Push1(s1, 0x02);
      var s3 := Push1(s2, 0x20);
      var s4 := MStore(s3);
      var s5 := Push0(s4);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x40c;
      var s12 := SLoad(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s14, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 70
    * Starting at 0x439
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x439 as nat
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
      var s5 := Push2(s4, 0x0444);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s6, gas - 1)
      else
        ExecuteFromCFGNode_s93(s6, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 71
    * Starting at 0x441
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x441 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 94
    * Segment Id for this node is: 72
    * Starting at 0x444
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x444 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x06);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0452);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s10, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 73
    * Starting at 0x452
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x452

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x452;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := Swap1(s4);
      var s6 := Swap2(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x452;
      var s12 := Push2(s11, 0x03c0);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s13, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 56
    * Starting at 0x3c0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x452

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x452;
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

  /** Node 97
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
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
      var s5 := Push2(s4, 0x039f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s479(s6, gas - 1)
      else
        ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 9
    * Starting at 0x63
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x03c9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s347(s5, gas - 1)
      else
        ExecuteFromCFGNode_s99(s5, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 10
    * Starting at 0x6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x03f8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s344(s5, gas - 1)
      else
        ExecuteFromCFGNode_s100(s5, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 11
    * Starting at 0x79
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x041a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s5, gas - 1)
      else
        ExecuteFromCFGNode_s101(s5, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 12
    * Starting at 0x84
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84 as nat
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

  /** Node 102
    * Segment Id for this node is: 66
    * Starting at 0x41a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41a as nat
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
      var s5 := Push2(s4, 0x0425);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s6, gas - 1)
      else
        ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 67
    * Starting at 0x422
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 104
    * Segment Id for this node is: 68
    * Starting at 0x425
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x425 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x03e8);
      var s4 := Push2(s3, 0x0434);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0bad);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s8, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 190
    * Starting at 0xbad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x434

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x434;
      assert s1.Peek(3) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0bbf);
      assert s11.Peek(0) == 0xbbf;
      assert s11.Peek(7) == 0x434;
      assert s11.Peek(8) == 0x3e8;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s12, gas - 1)
      else
        ExecuteFromCFGNode_s106(s12, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 191
    * Starting at 0xbbc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x434

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x434;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 107
    * Segment Id for this node is: 192
    * Starting at 0xbbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x434

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x434;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Push2(s1, 0x0bc8);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x0b6a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s5, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbc8

    requires s0.stack[7] == 0x434

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbc8;
      assert s1.Peek(7) == 0x434;
      assert s1.Peek(8) == 0x3e8;
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
      assert s11.Peek(4) == 0xbc8;
      assert s11.Peek(10) == 0x434;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s14, gas - 1)
      else
        ExecuteFromCFGNode_s109(s14, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xbc8

    requires s0.stack[8] == 0x434

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xbc8;
      assert s1.Peek(9) == 0x434;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 110
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xbc8

    requires s0.stack[8] == 0x434

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbc8;
      assert s1.Peek(8) == 0x434;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 193
    * Starting at 0xbc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x434

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x434;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0bd6);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0b6a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s9, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbd6

    requires s0.stack[7] == 0x434

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbd6;
      assert s1.Peek(7) == 0x434;
      assert s1.Peek(8) == 0x3e8;
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
      assert s11.Peek(4) == 0xbd6;
      assert s11.Peek(10) == 0x434;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s14, gas - 1)
      else
        ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xbd6

    requires s0.stack[8] == 0x434

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xbd6;
      assert s1.Peek(9) == 0x434;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xbd6

    requires s0.stack[8] == 0x434

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbd6;
      assert s1.Peek(8) == 0x434;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s5, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 194
    * Starting at 0xbd6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x434

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x434;
      assert s1.Peek(7) == 0x3e8;
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
      assert s11.Peek(4) == 0x434;
      assert s11.Peek(5) == 0x3e8;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s15, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 69
    * Starting at 0x434
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e8;
      var s2 := Push2(s1, 0x06d6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s3, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 112
    * Starting at 0x6d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e8;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x06e9);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0xff);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x0a);
      var s11 := Push2(s10, 0x0adf);
      assert s11.Peek(0) == 0xadf;
      assert s11.Peek(3) == 0x6e9;
      assert s11.Peek(8) == 0x3e8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s12, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x6e9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6e9;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s9, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x6e9

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6e9;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s318(s5, gas - 1)
      else
        ExecuteFromCFGNode_s120(s5, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6e9;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s4, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6e9;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s6, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x6e9

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6e9;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s7, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 113
    * Starting at 0x6e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x06f4);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x6f4

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6f4;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x6f4;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s14, gas - 1)
      else
        ExecuteFromCFGNode_s125(s14, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6f4

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x6f4;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s3, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x6f4

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x6f4;
      assert s1.Peek(9) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x6f4;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 127
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6f4

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6f4;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s6, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 114
    * Starting at 0x6f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x06fe);
      var s3 := Swap1(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0b0b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s6, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x6fe

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6fe;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s10, gas - 1)
      else
        ExecuteFromCFGNode_s130(s10, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6fe

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x6fe;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s3, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x6fe

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x6fe;
      assert s1.Peek(9) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x6fe;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 132
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x6fe

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6fe;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s6, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 115
    * Starting at 0x6fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup6(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x3e8;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x02);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Lt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(5) == 0x3e8;
      var s22 := Push2(s21, 0x0720);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s23, gas - 1)
      else
        ExecuteFromCFGNode_s134(s23, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 116
    * Starting at 0x71d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 135
    * Segment Id for this node is: 117
    * Starting at 0x720
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x720 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e8;
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
      assert s11.Peek(7) == 0x3e8;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Push1(s13, 0x20);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup4(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x3e8;
      var s22 := Caller(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := MStore(s26);
      var s28 := Dup2(s27);
      var s29 := Keccak256(s28);
      var s30 := Dup1(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(7) == 0x3e8;
      var s32 := Dup5(s31);
      var s33 := Swap3(s32);
      var s34 := Swap1(s33);
      var s35 := Push2(s34, 0x0752);
      var s36 := Swap1(s35);
      var s37 := Dup5(s36);
      var s38 := Swap1(s37);
      var s39 := Push2(s38, 0x09ec);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s40, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x752

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x752;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s10, gas - 1)
      else
        ExecuteFromCFGNode_s137(s10, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x752

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x752;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s3, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x752

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x752;
      assert s1.Peek(12) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x752;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 139
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x752

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x752;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s6, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 118
    * Starting at 0x752
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x752 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := SLoad(s7);
      var s9 := Push2(s8, 0x0768);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0xff);
      assert s11.Peek(2) == 0x768;
      assert s11.Peek(7) == 0x3e8;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x0a);
      var s14 := Push2(s13, 0x0adf);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s15, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x768

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x768;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s9, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x768

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x768;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s292(s5, gas - 1)
      else
        ExecuteFromCFGNode_s143(s5, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x768;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s4, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x768;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s6, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x768

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x768;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s7, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 119
    * Starting at 0x768
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x768 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x0773);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s6, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x773

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x773;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x773;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s14, gas - 1)
      else
        ExecuteFromCFGNode_s148(s14, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x773

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x773;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s3, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x773

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x773;
      assert s1.Peek(9) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x773;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 150
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x773

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x773;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s6, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 120
    * Starting at 0x773
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x773 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
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
      assert s11.Peek(8) == 0x3e8;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x03);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(11) == 0x3e8;
      var s22 := Keccak256(s21);
      var s23 := Push1(s22, 0x06);
      var s24 := SLoad(s23);
      var s25 := Push2(s24, 0x0100);
      var s26 := Swap1(s25);
      var s27 := Div(s26);
      var s28 := Swap1(s27);
      var s29 := Swap5(s28);
      var s30 := And(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(11) == 0x3e8;
      var s32 := MStore(s31);
      var s33 := Swap3(s32);
      var s34 := Swap1(s33);
      var s35 := MStore(s34);
      var s36 := Swap1(s35);
      var s37 := Dup2(s36);
      var s38 := Keccak256(s37);
      var s39 := Dup1(s38);
      var s40 := SLoad(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s152(s41, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 121
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Push2(s2, 0x07b1);
      var s4 := Swap1(s3);
      var s5 := Dup5(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x09ec);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s8, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x7b1

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7b1;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s10, gas - 1)
      else
        ExecuteFromCFGNode_s154(s10, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x7b1

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x7b1;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s3, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x7b1

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x7b1;
      assert s1.Peek(12) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x7b1;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 156
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x7b1

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7b1;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s6, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 122
    * Starting at 0x7b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := SLoad(s7);
      var s9 := Push2(s8, 0x07c7);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0xff);
      assert s11.Peek(2) == 0x7c7;
      assert s11.Peek(7) == 0x3e8;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x0a);
      var s14 := Push2(s13, 0x0adf);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s15, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x7c7

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7c7;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s9, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x7c7

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x7c7;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s266(s5, gas - 1)
      else
        ExecuteFromCFGNode_s160(s5, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x7c7;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s4, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x7c7;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s6, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x7c7

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7c7;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s7, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 123
    * Starting at 0x7c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x07d2);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s6, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x7d2

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7d2;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x7d2;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s14, gas - 1)
      else
        ExecuteFromCFGNode_s165(s14, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x7d2

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x7d2;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s3, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x7d2

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x7d2;
      assert s1.Peek(9) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x7d2;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 167
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x7d2

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7d2;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 124
    * Starting at 0x7d2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x07dc);
      var s3 := Swap1(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0b0b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s6, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x7dc

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7dc;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s10, gas - 1)
      else
        ExecuteFromCFGNode_s170(s10, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x7dc

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x7dc;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s3, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x7dc

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x7dc;
      assert s1.Peek(9) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x7dc;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 172
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x7dc

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7dc;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s6, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 125
    * Starting at 0x7dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup6(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x3e8;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x02);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup1(s18);
      var s20 := SLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(8) == 0x3e8;
      var s22 := Swap2(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0803);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x09ec);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s29, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x803

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x803;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s10, gas - 1)
      else
        ExecuteFromCFGNode_s175(s10, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x803

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x803;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s3, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x803

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x803;
      assert s1.Peek(12) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x803;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 177
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x803

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x803;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 126
    * Starting at 0x803
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x803 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x3e8;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Push0(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x02);
      var s19 := Push1(s18, 0x20);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(6) == 0x3e8;
      var s22 := Dup2(s21);
      var s23 := Keccak256(s22);
      var s24 := Dup1(s23);
      var s25 := SLoad(s24);
      var s26 := Dup5(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x082f);
      var s30 := Swap1(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(2) == 0x82f;
      assert s31.Peek(10) == 0x3e8;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0b0b);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s34, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x82f

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x82f;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s10, gas - 1)
      else
        ExecuteFromCFGNode_s180(s10, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x82f

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x82f;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s3, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x82f

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x82f;
      assert s1.Peek(12) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x82f;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 182
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x82f

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x82f;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s6, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 127
    * Starting at 0x82f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := SLoad(s7);
      var s9 := Push2(s8, 0x0845);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0xff);
      assert s11.Peek(2) == 0x845;
      assert s11.Peek(7) == 0x3e8;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x0a);
      var s14 := Push2(s13, 0x0adf);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s15, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x845

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x845;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s9, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x845

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x845;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s5, gas - 1)
      else
        ExecuteFromCFGNode_s186(s5, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x845;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s4, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x845;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s6, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x845

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x845;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s7, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 128
    * Starting at 0x845
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x845 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x0850);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s6, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x850

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x850;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x850;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s14, gas - 1)
      else
        ExecuteFromCFGNode_s191(s14, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x850

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x850;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s3, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x850

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x850;
      assert s1.Peek(9) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x850;
      assert s11.Peek(11) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 193
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x850

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x850;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s6, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 129
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0100);
      var s5 := Swap1(s4);
      var s6 := Div(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(7) == 0x3e8;
      var s12 := And(s11);
      var s13 := Push0(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x02);
      var s18 := Push1(s17, 0x20);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Dup2(s20);
      assert s21.Peek(8) == 0x3e8;
      var s22 := Keccak256(s21);
      var s23 := Dup1(s22);
      var s24 := SLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x087e);
      var s29 := Swap1(s28);
      var s30 := Dup5(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(2) == 0x87e;
      assert s31.Peek(10) == 0x3e8;
      var s32 := Push2(s31, 0x0b0b);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s33, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x87e

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x87e;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s10, gas - 1)
      else
        ExecuteFromCFGNode_s196(s10, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x87e

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x87e;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s3, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x87e

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x87e;
      assert s1.Peek(12) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x87e;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 198
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x87e

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x87e;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s6, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 130
    * Starting at 0x87e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x3e8;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(7) == 0x3e8;
      var s22 := And(s21);
      var s23 := Push0(s22);
      var s24 := Dup1(s23);
      var s25 := MLoad(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Push2(s26, 0x0c89);
      var s28 := Dup4(s27);
      var s29 := CodeCopy(s28);
      var s30 := Dup2(s29);
      var s31 := MLoad(s30);
      assert s31.Peek(9) == 0x3e8;
      var s32 := Swap2(s31);
      var s33 := MStore(s32);
      var s34 := Dup5(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MLoad(s35);
      var s37 := Push2(s36, 0x08b7);
      var s38 := Swap2(s37);
      var s39 := Dup2(s38);
      var s40 := MStore(s39);
      var s41 := Push1(s40, 0x20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s200(s41, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 131
    * Starting at 0x8b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x8b7

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(1) == 0x8b7;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Swap1(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s3, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 132
    * Starting at 0x8b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push1(s8, 0x06);
      var s10 := SLoad(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x3e8;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Dup3(s16);
      var s18 := Div(s17);
      var s19 := Dup2(s18);
      var s20 := And(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(7) == 0x3e8;
      var s22 := Swap1(s21);
      var s23 := Dup7(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := Push0(s25);
      var s27 := Dup1(s26);
      var s28 := MLoad(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Push2(s29, 0x0c89);
      var s31 := Dup4(s30);
      assert s31.Peek(12) == 0x3e8;
      var s32 := CodeCopy(s31);
      var s33 := Dup2(s32);
      var s34 := MLoad(s33);
      var s35 := Swap2(s34);
      var s36 := MStore(s35);
      var s37 := Swap1(s36);
      var s38 := Push2(s37, 0x08f3);
      var s39 := Swap1(s38);
      var s40 := Push1(s39, 0xff);
      var s41 := And(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s202(s41, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 133
    * Starting at 0x8ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x8f3

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0a);
      assert s1.Peek(2) == 0x8f3;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push2(s1, 0x0adf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s3, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x8f3

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8f3;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s9, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x8f3

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x8f3;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s214(s5, gas - 1)
      else
        ExecuteFromCFGNode_s205(s5, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x8f3;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s4, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x8f3;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s6, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x8f3

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x8f3;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s7, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 134
    * Starting at 0x8f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Push2(s1, 0x08fe);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s6, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x8fe

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8fe;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x8fe;
      assert s11.Peek(13) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s14, gas - 1)
      else
        ExecuteFromCFGNode_s210(s14, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x8fe

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x8fe;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s3, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x8fe

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x8fe;
      assert s1.Peek(12) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x8fe;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 212
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x8fe

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8fe;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s6, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 135
    * Starting at 0x8fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3e8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(10) == 0x3e8;
      var s12 := Swap2(s11);
      var s13 := Sub(s12);
      var s14 := Swap1(s13);
      var s15 := Log3(s14);
      var s16 := Pop(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Swap4(s17);
      var s19 := Swap3(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x3e8;
      var s22 := Pop(s21);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s23, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x8f3;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s4, gas - 1)
      else
        ExecuteFromCFGNode_s215(s4, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x8f3;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s4, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x8f3;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s7, gas - 1)
      else
        ExecuteFromCFGNode_s217(s7, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x8f3;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s5, gas - 1)
      else
        ExecuteFromCFGNode_s218(s5, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x8f3;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s2, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x8f3;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x8f3;
      assert s11.Peek(18) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s20, gas - 1)
      else
        ExecuteFromCFGNode_s220(s20, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x8f3;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s6, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x8f3

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x8f3;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s6, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x8f3

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x8f3;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s223(s4, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x8f3;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s7, gas - 1)
      else
        ExecuteFromCFGNode_s224(s7, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x8f3;
      assert s1.Peek(22) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s9, gas - 1)
      else
        ExecuteFromCFGNode_s225(s9, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x8f3;
      assert s1.Peek(22) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s3, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x8f3

    requires s0.stack[22] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x8f3;
      assert s1.Peek(22) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x8f3;
      assert s11.Peek(24) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 227
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x8f3;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s7, gas - 1)
      else
        ExecuteFromCFGNode_s228(s7, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x8f3;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s229(s4, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x8f3;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s11, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x8f3

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x8f3;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s8, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x8f3

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x8f3;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s10, gas - 1)
      else
        ExecuteFromCFGNode_s232(s10, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x8f3

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x8f3;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s3, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x8f3

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x8f3;
      assert s1.Peek(18) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x8f3;
      assert s11.Peek(20) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 234
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x8f3

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x8f3;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s8, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x8f3;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s7, gas - 1)
      else
        ExecuteFromCFGNode_s236(s7, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x8f3;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s3, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x8f3

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x8f3;
      assert s1.Peek(17) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x8f3;
      assert s11.Peek(19) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 238
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x8f3;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s8, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x8f3

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x8f3;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s7, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x845;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s4, gas - 1)
      else
        ExecuteFromCFGNode_s241(s4, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x845;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s4, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x845;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s265(s7, gas - 1)
      else
        ExecuteFromCFGNode_s243(s7, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x845;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s5, gas - 1)
      else
        ExecuteFromCFGNode_s244(s5, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x845;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s2, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x845;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x845;
      assert s11.Peek(15) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s20, gas - 1)
      else
        ExecuteFromCFGNode_s246(s20, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x845;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s6, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x845

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x845;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s6, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x845

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x845;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s249(s4, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x845;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s256(s7, gas - 1)
      else
        ExecuteFromCFGNode_s250(s7, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x845;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s9, gas - 1)
      else
        ExecuteFromCFGNode_s251(s9, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x845;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s3, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x845

    requires s0.stack[19] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x845;
      assert s1.Peek(19) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x845;
      assert s11.Peek(21) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 253
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x845;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s7, gas - 1)
      else
        ExecuteFromCFGNode_s254(s7, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x845;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s255(s4, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x845;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s11, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x845

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x845;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s8, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x845

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x845;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s10, gas - 1)
      else
        ExecuteFromCFGNode_s258(s10, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x845

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x845;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s3, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x845

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x845;
      assert s1.Peek(15) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x845;
      assert s11.Peek(17) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 260
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x845

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x845;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s8, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x845;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s264(s7, gas - 1)
      else
        ExecuteFromCFGNode_s262(s7, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x845;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s3, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x845

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x845;
      assert s1.Peek(14) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x845;
      assert s11.Peek(16) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 264
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x845;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s8, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x845

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x845;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s7, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x7c7;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s4, gas - 1)
      else
        ExecuteFromCFGNode_s267(s4, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x7c7;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s4, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x7c7;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s7, gas - 1)
      else
        ExecuteFromCFGNode_s269(s7, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x7c7;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s5, gas - 1)
      else
        ExecuteFromCFGNode_s270(s5, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x7c7;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s2, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x7c7;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x7c7;
      assert s11.Peek(15) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s273(s20, gas - 1)
      else
        ExecuteFromCFGNode_s272(s20, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x7c7;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s6, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x7c7

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x7c7;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s6, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x7c7

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x7c7;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s275(s4, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x7c7;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s7, gas - 1)
      else
        ExecuteFromCFGNode_s276(s7, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x7c7;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s279(s9, gas - 1)
      else
        ExecuteFromCFGNode_s277(s9, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x7c7;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s3, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x7c7

    requires s0.stack[19] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x7c7;
      assert s1.Peek(19) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x7c7;
      assert s11.Peek(21) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 279
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x7c7;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s7, gas - 1)
      else
        ExecuteFromCFGNode_s280(s7, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x7c7;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s281(s4, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x7c7;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s11, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x7c7

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x7c7;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s8, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x7c7

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x7c7;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s286(s10, gas - 1)
      else
        ExecuteFromCFGNode_s284(s10, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x7c7

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x7c7;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s3, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x7c7

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x7c7;
      assert s1.Peek(15) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x7c7;
      assert s11.Peek(17) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 286
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x7c7

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x7c7;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s8, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x7c7;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s290(s7, gas - 1)
      else
        ExecuteFromCFGNode_s288(s7, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x7c7;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s3, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x7c7

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x7c7;
      assert s1.Peek(14) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x7c7;
      assert s11.Peek(16) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 290
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x7c7;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s8, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x7c7

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x7c7;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s7, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x768;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s4, gas - 1)
      else
        ExecuteFromCFGNode_s293(s4, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x768;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s4, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x768;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s317(s7, gas - 1)
      else
        ExecuteFromCFGNode_s295(s7, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x768;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s313(s5, gas - 1)
      else
        ExecuteFromCFGNode_s296(s5, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x768;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s2, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x768;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x768;
      assert s11.Peek(15) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s299(s20, gas - 1)
      else
        ExecuteFromCFGNode_s298(s20, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x768;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s6, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x768

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x768;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s6, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x768

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x768;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s301(s4, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x768;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s308(s7, gas - 1)
      else
        ExecuteFromCFGNode_s302(s7, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x768;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s305(s9, gas - 1)
      else
        ExecuteFromCFGNode_s303(s9, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x768;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s3, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x768

    requires s0.stack[19] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x768;
      assert s1.Peek(19) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x768;
      assert s11.Peek(21) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 305
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x768;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s7, gas - 1)
      else
        ExecuteFromCFGNode_s306(s7, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x768;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s307(s4, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x768;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s11, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x768

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x768;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s8, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x768

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x768;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s312(s10, gas - 1)
      else
        ExecuteFromCFGNode_s310(s10, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x768

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x768;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s3, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x768

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x768;
      assert s1.Peek(15) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x768;
      assert s11.Peek(17) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 312
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x768

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x768;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s8, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x768;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s316(s7, gas - 1)
      else
        ExecuteFromCFGNode_s314(s7, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x768;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s3, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x768

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x768;
      assert s1.Peek(14) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x768;
      assert s11.Peek(16) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 316
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x768;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s8, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x768

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x768;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s7, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6e9;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s4, gas - 1)
      else
        ExecuteFromCFGNode_s319(s4, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6e9;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s4, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6e9;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s7, gas - 1)
      else
        ExecuteFromCFGNode_s321(s7, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6e9;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s339(s5, gas - 1)
      else
        ExecuteFromCFGNode_s322(s5, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6e9;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s2, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6e9;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x6e9;
      assert s11.Peek(15) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s325(s20, gas - 1)
      else
        ExecuteFromCFGNode_s324(s20, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6e9;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s6, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6e9

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6e9;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s6, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x6e9

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x6e9;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s327(s4, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6e9;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s7, gas - 1)
      else
        ExecuteFromCFGNode_s328(s7, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x6e9;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s331(s9, gas - 1)
      else
        ExecuteFromCFGNode_s329(s9, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x6e9;
      assert s1.Peek(19) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s3, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x6e9

    requires s0.stack[19] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x6e9;
      assert s1.Peek(19) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x6e9;
      assert s11.Peek(21) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 331
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6e9;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s333(s7, gas - 1)
      else
        ExecuteFromCFGNode_s332(s7, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6e9;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s333(s4, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6e9;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s11, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6e9

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6e9;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s8, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6e9

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6e9;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s338(s10, gas - 1)
      else
        ExecuteFromCFGNode_s336(s10, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6e9

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x6e9;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s3, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x6e9

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x6e9;
      assert s1.Peek(15) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x6e9;
      assert s11.Peek(17) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 338
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6e9

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6e9;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s8, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6e9;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s342(s7, gas - 1)
      else
        ExecuteFromCFGNode_s340(s7, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6e9;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s3, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6e9

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6e9;
      assert s1.Peek(14) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x6e9;
      assert s11.Peek(16) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 342
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6e9;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s8, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6e9

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6e9;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s7, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 62
    * Starting at 0x3f8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f8 as nat
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
      var s5 := Push2(s4, 0x0403);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s6, gas - 1)
      else
        ExecuteFromCFGNode_s345(s6, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 63
    * Starting at 0x400
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x400 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 346
    * Segment Id for this node is: 64
    * Starting at 0x403
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x403 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x040c);
      var s4 := Push0(s3);
      var s5 := SLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s7, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 57
    * Starting at 0x3c9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c9 as nat
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
      var s5 := Push2(s4, 0x03d4);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s6, gas - 1)
      else
        ExecuteFromCFGNode_s348(s6, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 58
    * Starting at 0x3d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 349
    * Segment Id for this node is: 59
    * Starting at 0x3d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x03e8);
      var s4 := Push2(s3, 0x03e3);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0b85);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s8, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 186
    * Starting at 0xb85
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x3e3

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e3;
      assert s1.Peek(3) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0b96);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s352(s11, gas - 1)
      else
        ExecuteFromCFGNode_s351(s11, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 187
    * Starting at 0xb93
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x3e3

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x3e3;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 352
    * Segment Id for this node is: 188
    * Starting at 0xb96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x3e3

    requires s0.stack[5] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e3;
      assert s1.Peek(5) == 0x3e8;
      var s2 := Push2(s1, 0x0b9f);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0b6a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s5, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 183
    * Starting at 0xb6a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xb9f

    requires s0.stack[6] == 0x3e3

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb9f;
      assert s1.Peek(6) == 0x3e3;
      assert s1.Peek(7) == 0x3e8;
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
      assert s11.Peek(4) == 0xb9f;
      assert s11.Peek(9) == 0x3e3;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0b80);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s355(s14, gas - 1)
      else
        ExecuteFromCFGNode_s354(s14, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 184
    * Starting at 0xb7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb9f

    requires s0.stack[7] == 0x3e3

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(3) == 0xb9f;
      assert s1.Peek(8) == 0x3e3;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 355
    * Segment Id for this node is: 185
    * Starting at 0xb80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xb9f

    requires s0.stack[7] == 0x3e3

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb9f;
      assert s1.Peek(7) == 0x3e3;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s5, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 189
    * Starting at 0xb9f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x3e3

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3e3;
      assert s1.Peek(6) == 0x3e8;
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
      assert s11.Peek(1) == 0x3e3;
      assert s11.Peek(4) == 0x3e8;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s13, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 60
    * Starting at 0x3e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e8;
      var s2 := Push2(s1, 0x0584);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s3, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 98
    * Starting at 0x584
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x584 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3e8;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0597);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0xff);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x0a);
      var s11 := Push2(s10, 0x0adf);
      assert s11.Peek(0) == 0xadf;
      assert s11.Peek(3) == 0x597;
      assert s11.Peek(7) == 0x3e8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s12, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x597

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x597;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s9, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x597

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x597;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s453(s5, gas - 1)
      else
        ExecuteFromCFGNode_s361(s5, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x597;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s4, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x597;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s6, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x597

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x597;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s7, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 99
    * Starting at 0x597
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x597 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Push2(s1, 0x05a2);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s6, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x5a2

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a2;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x5a2;
      assert s11.Peek(9) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s368(s14, gas - 1)
      else
        ExecuteFromCFGNode_s366(s14, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x5a2

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x5a2;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s3, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x5a2

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x5a2;
      assert s1.Peek(8) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x5a2;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 368
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x5a2

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a2;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s6, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 100
    * Starting at 0x5a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Push2(s1, 0x05ac);
      var s3 := Swap1(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0b0b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s6, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x5ac

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5ac;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s373(s10, gas - 1)
      else
        ExecuteFromCFGNode_s371(s10, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x5ac

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s3, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x5ac

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x5ac;
      assert s1.Peek(8) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x5ac;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 373
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x5ac

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ac;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s6, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 101
    * Starting at 0x5ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x3e8;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Lt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x05c5);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s376(s17, gas - 1)
      else
        ExecuteFromCFGNode_s375(s17, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 102
    * Starting at 0x5c2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 376
    * Segment Id for this node is: 103
    * Starting at 0x5c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3e8;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x03);
      var s8 := Push1(s7, 0x20);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x3e8;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Keccak256(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(9) == 0x3e8;
      var s22 := And(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := MStore(s26);
      var s28 := Swap1(s27);
      var s29 := Keccak256(s28);
      var s30 := Dup3(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x3e8;
      var s32 := SStore(s31);
      var s33 := Push1(s32, 0x06);
      var s34 := SLoad(s33);
      var s35 := Push2(s34, 0x05fb);
      var s36 := Swap1(s35);
      var s37 := Push1(s36, 0xff);
      var s38 := And(s37);
      var s39 := Push1(s38, 0x0a);
      var s40 := Push2(s39, 0x0adf);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s41, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x5fb

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5fb;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s9, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x5fb

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x5fb;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s427(s5, gas - 1)
      else
        ExecuteFromCFGNode_s379(s5, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x5fb;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s4, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x5fb;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s6, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x5fb

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5fb;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s7, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 104
    * Starting at 0x5fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Push2(s1, 0x0606);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s6, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x606

    requires s0.stack[6] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x606;
      assert s1.Peek(6) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x606;
      assert s11.Peek(9) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s386(s14, gas - 1)
      else
        ExecuteFromCFGNode_s384(s14, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x606

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x606;
      assert s1.Peek(8) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s3, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x606

    requires s0.stack[8] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x606;
      assert s1.Peek(8) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x606;
      assert s11.Peek(10) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 386
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x606

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x606;
      assert s1.Peek(7) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s6, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 105
    * Starting at 0x606
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x606 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3e8;
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x03);
      var s8 := Push1(s7, 0x20);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x3e8;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Keccak256(s14);
      var s16 := Push1(s15, 0x06);
      var s17 := SLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(12) == 0x3e8;
      var s22 := Sub(s21);
      var s23 := Push2(s22, 0x0100);
      var s24 := Swap1(s23);
      var s25 := Swap2(s24);
      var s26 := Div(s25);
      var s27 := Dup2(s26);
      var s28 := And(s27);
      var s29 := Dup6(s28);
      var s30 := MStore(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(10) == 0x3e8;
      var s32 := Dup4(s31);
      var s33 := MStore(s32);
      var s34 := Swap3(s33);
      var s35 := Dup2(s34);
      var s36 := Swap1(s35);
      var s37 := Keccak256(s36);
      var s38 := Swap5(s37);
      var s39 := Swap1(s38);
      var s40 := Swap5(s39);
      var s41 := SStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s388(s41, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 106
    * Starting at 0x638
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x638 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap3(s0);
      assert s1.Peek(7) == 0x3e8;
      var s2 := MLoad(s1);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Swap1(s5);
      var s7 := Dup7(s6);
      var s8 := And(s7);
      var s9 := Swap3(s8);
      var s10 := Push32(s9, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s11 := Swap2(s10);
      assert s11.Peek(8) == 0x3e8;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Swap2(s15);
      var s17 := Sub(s16);
      var s18 := Swap1(s17);
      var s19 := Log3(s18);
      var s20 := Push1(s19, 0x06);
      var s21 := SLoad(s20);
      assert s21.Peek(4) == 0x3e8;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0x01);
      var s24 := Push1(s23, 0xa0);
      var s25 := Shl(s24);
      var s26 := Sub(s25);
      var s27 := Push2(s26, 0x0100);
      var s28 := Dup3(s27);
      var s29 := Div(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x3e8;
      var s32 := Caller(s31);
      var s33 := Swap1(s32);
      var s34 := Push32(s33, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s35 := Swap1(s34);
      var s36 := Push2(s35, 0x06af);
      var s37 := Swap1(s36);
      var s38 := Push1(s37, 0xff);
      var s39 := And(s38);
      var s40 := Push1(s39, 0x0a);
      var s41 := Push2(s40, 0x0adf);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s389(s41, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 107
    * Starting at 0x6ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0xadf

    requires s0.stack[3] == 0x6af

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s1, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x6af

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6af;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s9, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x6af

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6af;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s401(s5, gas - 1)
      else
        ExecuteFromCFGNode_s392(s5, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6af;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s4, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6af;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s6, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x6af

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6af;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s7, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 108
    * Starting at 0x6af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push2(s1, 0x06ba);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s6, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x6ba

    requires s0.stack[9] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6ba;
      assert s1.Peek(9) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x6ba;
      assert s11.Peek(12) == 0x3e8;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s399(s14, gas - 1)
      else
        ExecuteFromCFGNode_s397(s14, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x6ba

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x6ba;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s3, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x6ba

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x6ba;
      assert s1.Peek(11) == 0x3e8;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x6ba;
      assert s11.Peek(13) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 399
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x6ba

    requires s0.stack[10] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6ba;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s6, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 109
    * Starting at 0x6ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3e8;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s49(s8, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6af;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s403(s4, gas - 1)
      else
        ExecuteFromCFGNode_s402(s4, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6af;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s4, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6af;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s426(s7, gas - 1)
      else
        ExecuteFromCFGNode_s404(s7, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6af;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s422(s5, gas - 1)
      else
        ExecuteFromCFGNode_s405(s5, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6af;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s2, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6af;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x6af;
      assert s11.Peek(17) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s408(s20, gas - 1)
      else
        ExecuteFromCFGNode_s407(s20, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x6af;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s6, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x6af

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x6af;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s409(s6, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x6af

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x6af;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s410(s4, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6af;
      assert s1.Peek(20) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s417(s7, gas - 1)
      else
        ExecuteFromCFGNode_s411(s7, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x6af;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s414(s9, gas - 1)
      else
        ExecuteFromCFGNode_s412(s9, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x6af;
      assert s1.Peek(21) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s3, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x6af

    requires s0.stack[21] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x6af;
      assert s1.Peek(21) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x6af;
      assert s11.Peek(23) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 414
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6af;
      assert s1.Peek(20) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s416(s7, gas - 1)
      else
        ExecuteFromCFGNode_s415(s7, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6af;
      assert s1.Peek(20) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s416(s4, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6af;
      assert s1.Peek(20) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s11, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x6af

    requires s0.stack[20] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x6af;
      assert s1.Peek(20) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s8, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6af

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6af;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s421(s10, gas - 1)
      else
        ExecuteFromCFGNode_s419(s10, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6af

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x6af;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s3, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x6af

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x6af;
      assert s1.Peek(17) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x6af;
      assert s11.Peek(19) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 421
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6af

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6af;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s8, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6af;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s425(s7, gas - 1)
      else
        ExecuteFromCFGNode_s423(s7, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6af;
      assert s1.Peek(16) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s3, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x6af

    requires s0.stack[16] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x6af;
      assert s1.Peek(16) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x6af;
      assert s11.Peek(18) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 425
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6af;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s8, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x6af

    requires s0.stack[15] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x6af;
      assert s1.Peek(15) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s7, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x5fb;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s4, gas - 1)
      else
        ExecuteFromCFGNode_s428(s4, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x5fb;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s4, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x5fb;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s452(s7, gas - 1)
      else
        ExecuteFromCFGNode_s430(s7, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x5fb;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s448(s5, gas - 1)
      else
        ExecuteFromCFGNode_s431(s5, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x5fb;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s2, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x5fb;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x5fb;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s434(s20, gas - 1)
      else
        ExecuteFromCFGNode_s433(s20, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x5fb;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s6, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x5fb

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x5fb;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s6, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x5fb

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x5fb;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s436(s4, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x5fb;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s443(s7, gas - 1)
      else
        ExecuteFromCFGNode_s437(s7, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x5fb;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s440(s9, gas - 1)
      else
        ExecuteFromCFGNode_s438(s9, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x5fb;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s3, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x5fb

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x5fb;
      assert s1.Peek(18) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x5fb;
      assert s11.Peek(20) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 440
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x5fb;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s442(s7, gas - 1)
      else
        ExecuteFromCFGNode_s441(s7, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x5fb;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s442(s4, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x5fb;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s11, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x5fb

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x5fb;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s8, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x5fb

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x5fb;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s447(s10, gas - 1)
      else
        ExecuteFromCFGNode_s445(s10, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x5fb

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x5fb;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s3, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x5fb

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x5fb;
      assert s1.Peek(14) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x5fb;
      assert s11.Peek(16) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 447
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x5fb

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x5fb;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s8, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x5fb;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s451(s7, gas - 1)
      else
        ExecuteFromCFGNode_s449(s7, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x5fb;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s3, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x5fb

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x5fb;
      assert s1.Peek(13) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x5fb;
      assert s11.Peek(15) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 451
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x5fb;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s8, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x5fb

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x5fb;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s7, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x597;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s455(s4, gas - 1)
      else
        ExecuteFromCFGNode_s454(s4, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x597;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s4, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x597;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s478(s7, gas - 1)
      else
        ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x597;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s474(s5, gas - 1)
      else
        ExecuteFromCFGNode_s457(s5, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x597;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s2, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x597;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x597;
      assert s11.Peek(14) == 0x3e8;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s460(s20, gas - 1)
      else
        ExecuteFromCFGNode_s459(s20, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x597;
      assert s1.Peek(10) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s6, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x597

    requires s0.stack[11] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x597;
      assert s1.Peek(11) == 0x3e8;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s6, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x597

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x597;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s462(s4, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x597;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s469(s7, gas - 1)
      else
        ExecuteFromCFGNode_s463(s7, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x597;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s9, gas - 1)
      else
        ExecuteFromCFGNode_s464(s9, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x597;
      assert s1.Peek(18) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s3, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x597

    requires s0.stack[18] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x597;
      assert s1.Peek(18) == 0x3e8;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x597;
      assert s11.Peek(20) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 466
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x597;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s468(s7, gas - 1)
      else
        ExecuteFromCFGNode_s467(s7, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x597;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s468(s4, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x597;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s11, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x597

    requires s0.stack[17] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x597;
      assert s1.Peek(17) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s8, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x597

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x597;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s473(s10, gas - 1)
      else
        ExecuteFromCFGNode_s471(s10, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x597

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x597;
      assert s1.Peek(14) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s3, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x597

    requires s0.stack[14] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x597;
      assert s1.Peek(14) == 0x3e8;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x597;
      assert s11.Peek(16) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 473
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x597

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x597;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s8, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x597;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s477(s7, gas - 1)
      else
        ExecuteFromCFGNode_s475(s7, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x597;
      assert s1.Peek(13) == 0x3e8;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s3, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x597

    requires s0.stack[13] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x597;
      assert s1.Peek(13) == 0x3e8;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x597;
      assert s11.Peek(15) == 0x3e8;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 477
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x597;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s8, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x597

    requires s0.stack[12] == 0x3e8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x597;
      assert s1.Peek(12) == 0x3e8;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s7, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 52
    * Starting at 0x39f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
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
      var s5 := Push2(s4, 0x03aa);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s481(s6, gas - 1)
      else
        ExecuteFromCFGNode_s480(s6, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 53
    * Starting at 0x3a7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 481
    * Segment Id for this node is: 54
    * Starting at 0x3aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x03b3);
      var s4 := Push2(s3, 0x04f8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s5, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 89
    * Starting at 0x4f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x3b3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3b3;
      var s2 := Push1(s1, 0x04);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x0505);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0c30);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s8, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 13
    * Starting at 0x87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x039b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s743(s4, gas - 1)
      else
        ExecuteFromCFGNode_s484(s4, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 14
    * Starting at 0x8d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallValue(s0);
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0243);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s672(s4, gas - 1)
      else
        ExecuteFromCFGNode_s485(s4, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 15
    * Starting at 0x93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Push2(s1, 0x009e);
      var s3 := Push1(s2, 0xc8);
      var s4 := CallValue(s3);
      var s5 := Push2(s4, 0x09cd);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s486(s6, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 143
    * Starting at 0x9cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x9e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9e;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09e7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s488(s5, gas - 1)
      else
        ExecuteFromCFGNode_s487(s5, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 144
    * Starting at 0x9d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x9e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x9e;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 488
    * Segment Id for this node is: 145
    * Starting at 0x9e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x9e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9e;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s5, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 16
    * Starting at 0x9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x00ab);
      var s6 := Dup3(s5);
      var s7 := CallValue(s6);
      var s8 := Push2(s7, 0x09ec);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s9, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s493(s10, gas - 1)
      else
        ExecuteFromCFGNode_s491(s10, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0xab;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s3, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0xab;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0xab;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 493
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xab

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s494(s6, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 17
    * Starting at 0xab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push0(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x00c1);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0xff);
      assert s11.Peek(2) == 0xc1;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x0a);
      var s14 := Push2(s13, 0x0adf);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s15, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc1;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s9, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xc1;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s646(s5, gas - 1)
      else
        ExecuteFromCFGNode_s497(s5, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xc1;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s4, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xc1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s6, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc1;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s7, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 18
    * Starting at 0xc1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x00ce);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0af4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s8, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xce;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0xce;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s504(s14, gas - 1)
      else
        ExecuteFromCFGNode_s502(s14, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0xce;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s3, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0xce;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0xce;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 504
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xce;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s505(s6, gas - 1)
  }

  /** Node 505
    * Segment Id for this node is: 19
    * Starting at 0xce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x00db);
      var s6 := Dup3(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x09cd);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s9, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 143
    * Starting at 0x9cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09e7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s508(s5, gas - 1)
      else
        ExecuteFromCFGNode_s507(s5, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 144
    * Starting at 0x9d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0xdb;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 508
    * Segment Id for this node is: 145
    * Starting at 0x9e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s509(s5, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 20
    * Starting at 0xdb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x00ef);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0xff);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x0a);
      assert s11.Peek(2) == 0xef;
      var s12 := Push2(s11, 0x0adf);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s13, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xef;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s9, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xef;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s620(s5, gas - 1)
      else
        ExecuteFromCFGNode_s512(s5, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xef;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s4, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xef;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s6, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xef;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s7, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 21
    * Starting at 0xef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f9);
      var s3 := Swap1(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s516(s6, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xf9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0xf9;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s519(s14, gas - 1)
      else
        ExecuteFromCFGNode_s517(s14, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xf9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0xf9;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s3, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0xf9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0xf9;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0xf9;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 519
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xf9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s6, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 22
    * Starting at 0xf9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x02);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      var s9 := Dup1(s8);
      var s10 := MLoad(s9);
      var s11 := Push1(s10, 0x20);
      var s12 := Push2(s11, 0x0c69);
      var s13 := Dup4(s12);
      var s14 := CodeCopy(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Swap2(s16);
      var s18 := MStore(s17);
      var s19 := SLoad(s18);
      var s20 := Lt(s19);
      var s21 := IsZero(s20);
      var s22 := Push2(s21, 0x011a);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s522(s23, gas - 1)
      else
        ExecuteFromCFGNode_s521(s23, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 23
    * Starting at 0x117
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

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

  /** Node 522
    * Segment Id for this node is: 24
    * Starting at 0x11a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x012b);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x0a);
      var s9 := Push2(s8, 0x0adf);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s10, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s9, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x12b;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s594(s5, gas - 1)
      else
        ExecuteFromCFGNode_s525(s5, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s4, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x12b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s6, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x12b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s528(s7, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 25
    * Starting at 0x12b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0135);
      var s3 := Swap1(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s6, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x135

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x135;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x135;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s532(s14, gas - 1)
      else
        ExecuteFromCFGNode_s530(s14, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x135

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x135;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s531(s3, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x135

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x135;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x135;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 532
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x135

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x135;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s533(s6, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 26
    * Starting at 0x135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup2(s10);
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0153);
      var s19 := Swap1(s18);
      var s20 := Dup5(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x153;
      var s22 := Push2(s21, 0x0b0b);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s534(s23, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x153;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s537(s10, gas - 1)
      else
        ExecuteFromCFGNode_s535(s10, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x153;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s3, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x153;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x153;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 537
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x153;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s6, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 27
    * Starting at 0x153
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := SLoad(s7);
      var s9 := Push2(s8, 0x0169);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0xff);
      assert s11.Peek(2) == 0x169;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x0a);
      var s14 := Push2(s13, 0x0adf);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s15, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x169;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s9, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x169;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s568(s5, gas - 1)
      else
        ExecuteFromCFGNode_s541(s5, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x169;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s4, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x169;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s543(s6, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x169;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s7, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 28
    * Starting at 0x169
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x169 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0173);
      var s3 := Swap1(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0af4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s6, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x173;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x173;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s548(s14, gas - 1)
      else
        ExecuteFromCFGNode_s546(s14, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x173;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s3, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x173;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x173;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 548
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x173

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x173;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s6, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 29
    * Starting at 0x173
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x173 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup1(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push0(s8);
      var s10 := Dup1(s9);
      var s11 := MLoad(s10);
      var s12 := Push1(s11, 0x20);
      var s13 := Push2(s12, 0x0c69);
      var s14 := Dup4(s13);
      var s15 := CodeCopy(s14);
      var s16 := Dup2(s15);
      var s17 := MLoad(s16);
      var s18 := Swap2(s17);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := SLoad(s20);
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x019a);
      var s26 := Swap1(s25);
      var s27 := Dup5(s26);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x09ec);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s30, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x19a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x19a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s553(s10, gas - 1)
      else
        ExecuteFromCFGNode_s551(s10, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x19a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x19a;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s552(s3, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x19a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x19a;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x19a;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 553
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x19a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x19a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s6, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 30
    * Starting at 0x19a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x06);
      var s8 := SLoad(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0100);
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Div(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := And(s19);
      var s21 := Swap1(s20);
      var s22 := Push2(s21, 0x1388);
      var s23 := Swap1(s22);
      var s24 := Dup7(s23);
      var s25 := Swap1(s24);
      var s26 := Push0(s25);
      var s27 := Push1(s26, 0x40);
      var s28 := MLoad(s27);
      var s29 := Dup1(s28);
      var s30 := Dup4(s29);
      var s31 := Sub(s30);
      var s32 := Dup2(s31);
      var s33 := Dup6(s32);
      var s34 := Dup9(s33);
      var s35 := Dup9(s34);
      var s36 := Call(s35);
      var s37 := Swap4(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Pop(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s555(s41, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 31
    * Starting at 0x1cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x01f6);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s567(s7, gas - 1)
      else
        ExecuteFromCFGNode_s556(s7, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 32
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push0(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x01fb);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s25, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 34
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x01);
      var s7 := SLoad(s6);
      var s8 := Push2(s7, 0x020d);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x09cd);
      assert s11.Peek(0) == 0x9cd;
      assert s11.Peek(3) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s558(s12, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 143
    * Starting at 0x9cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09e7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s560(s5, gas - 1)
      else
        ExecuteFromCFGNode_s559(s5, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 144
    * Starting at 0x9d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 560
    * Segment Id for this node is: 145
    * Starting at 0x9e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s561(s5, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 35
    * Starting at 0x20d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x021a);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0b0b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s8, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x21a;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s565(s10, gas - 1)
      else
        ExecuteFromCFGNode_s563(s10, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x21a;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s3, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x21a;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x21a;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 565
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x21a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x21a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s6, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 36
    * Starting at 0x21a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := SStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Caller(s8);
      var s10 := Swap1(s9);
      var s11 := Push0(s10);
      var s12 := Swap1(s11);
      var s13 := Push0(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Push2(s16, 0x0c89);
      var s18 := Dup4(s17);
      var s19 := CodeCopy(s18);
      var s20 := Dup2(s19);
      var s21 := MLoad(s20);
      var s22 := Swap2(s21);
      var s23 := MStore(s22);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x40);
      var s28 := MLoad(s27);
      var s29 := Dup1(s28);
      var s30 := Swap2(s29);
      var s31 := Sub(s30);
      var s32 := Swap1(s31);
      var s33 := Log3(s32);
      var s34 := Stop(s33);
      // Segment is terminal (Revert, Stop or Return)
      s34
  }

  /** Node 567
    * Segment Id for this node is: 33
    * Starting at 0x1f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s557(s4, gas - 1)
  }

  /** Node 568
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x169;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s570(s4, gas - 1)
      else
        ExecuteFromCFGNode_s569(s4, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x169;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s4, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x169;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s593(s7, gas - 1)
      else
        ExecuteFromCFGNode_s571(s7, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x169;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s589(s5, gas - 1)
      else
        ExecuteFromCFGNode_s572(s5, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x169;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s573(s2, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x169;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x169;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s575(s20, gas - 1)
      else
        ExecuteFromCFGNode_s574(s20, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x169;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s6, gas - 1)
  }

  /** Node 575
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x169;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s576(s6, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x169;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s577(s4, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x169;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s584(s7, gas - 1)
      else
        ExecuteFromCFGNode_s578(s7, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x169;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s581(s9, gas - 1)
      else
        ExecuteFromCFGNode_s579(s9, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x169;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s580(s3, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x169;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x169;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 581
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x169;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s583(s7, gas - 1)
      else
        ExecuteFromCFGNode_s582(s7, gas - 1)
  }

  /** Node 582
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x169;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s583(s4, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x169;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s577(s11, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x169;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s585(s8, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x169;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s588(s10, gas - 1)
      else
        ExecuteFromCFGNode_s586(s10, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x169;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s587(s3, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x169;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x169;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 588
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x169;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s543(s8, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x169;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s592(s7, gas - 1)
      else
        ExecuteFromCFGNode_s590(s7, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x169;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s591(s3, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x169;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x169;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 592
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x169;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s8, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x169

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x169;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s7, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s596(s4, gas - 1)
      else
        ExecuteFromCFGNode_s595(s4, gas - 1)
  }

  /** Node 595
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x12b;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s4, gas - 1)
  }

  /** Node 596
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s619(s7, gas - 1)
      else
        ExecuteFromCFGNode_s597(s7, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s615(s5, gas - 1)
      else
        ExecuteFromCFGNode_s598(s5, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x12b;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s599(s2, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x12b;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s601(s20, gas - 1)
      else
        ExecuteFromCFGNode_s600(s20, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s6, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s6, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s603(s4, gas - 1)
  }

  /** Node 603
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s610(s7, gas - 1)
      else
        ExecuteFromCFGNode_s604(s7, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x12b;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s607(s9, gas - 1)
      else
        ExecuteFromCFGNode_s605(s9, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x12b;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s606(s3, gas - 1)
  }

  /** Node 606
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x12b;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x12b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 607
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s607(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s609(s7, gas - 1)
      else
        ExecuteFromCFGNode_s608(s7, gas - 1)
  }

  /** Node 608
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s608(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s609(s4, gas - 1)
  }

  /** Node 609
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s609(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x12b;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s603(s11, gas - 1)
  }

  /** Node 610
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s610(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s611(s8, gas - 1)
  }

  /** Node 611
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s611(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s614(s10, gas - 1)
      else
        ExecuteFromCFGNode_s612(s10, gas - 1)
  }

  /** Node 612
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s612(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x12b;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s613(s3, gas - 1)
  }

  /** Node 613
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s613(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x12b;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x12b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 614
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s614(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x12b;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s8, gas - 1)
  }

  /** Node 615
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s615(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s618(s7, gas - 1)
      else
        ExecuteFromCFGNode_s616(s7, gas - 1)
  }

  /** Node 616
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s616(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x12b;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s617(s3, gas - 1)
  }

  /** Node 617
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s617(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x12b;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x12b;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 618
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s618(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s8, gas - 1)
  }

  /** Node 619
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s619(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s7, gas - 1)
  }

  /** Node 620
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s620(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s622(s4, gas - 1)
      else
        ExecuteFromCFGNode_s621(s4, gas - 1)
  }

  /** Node 621
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s621(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xef;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s4, gas - 1)
  }

  /** Node 622
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s622(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s645(s7, gas - 1)
      else
        ExecuteFromCFGNode_s623(s7, gas - 1)
  }

  /** Node 623
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s623(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s641(s5, gas - 1)
      else
        ExecuteFromCFGNode_s624(s5, gas - 1)
  }

  /** Node 624
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s624(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xef;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s625(s2, gas - 1)
  }

  /** Node 625
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s625(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xef;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0xef;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s627(s20, gas - 1)
      else
        ExecuteFromCFGNode_s626(s20, gas - 1)
  }

  /** Node 626
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s626(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s6, gas - 1)
  }

  /** Node 627
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s627(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xef;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s628(s6, gas - 1)
  }

  /** Node 628
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s628(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0xef;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s629(s4, gas - 1)
  }

  /** Node 629
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s629(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xef;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s636(s7, gas - 1)
      else
        ExecuteFromCFGNode_s630(s7, gas - 1)
  }

  /** Node 630
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s630(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0xef;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s633(s9, gas - 1)
      else
        ExecuteFromCFGNode_s631(s9, gas - 1)
  }

  /** Node 631
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s631(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0xef;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s632(s3, gas - 1)
  }

  /** Node 632
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s632(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0xef;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0xef;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 633
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s633(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xef;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s635(s7, gas - 1)
      else
        ExecuteFromCFGNode_s634(s7, gas - 1)
  }

  /** Node 634
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s634(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s635(s4, gas - 1)
  }

  /** Node 635
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s635(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xef;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s629(s11, gas - 1)
  }

  /** Node 636
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s636(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xef;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s637(s8, gas - 1)
  }

  /** Node 637
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s637(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xef;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s640(s10, gas - 1)
      else
        ExecuteFromCFGNode_s638(s10, gas - 1)
  }

  /** Node 638
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s638(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0xef;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s639(s3, gas - 1)
  }

  /** Node 639
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s639(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0xef;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0xef;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 640
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s640(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xef;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s514(s8, gas - 1)
  }

  /** Node 641
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s641(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xef;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s644(s7, gas - 1)
      else
        ExecuteFromCFGNode_s642(s7, gas - 1)
  }

  /** Node 642
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s642(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xef;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s643(s3, gas - 1)
  }

  /** Node 643
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s643(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xef;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0xef;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 644
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s644(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xef;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s8, gas - 1)
  }

  /** Node 645
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s645(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xef;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s7, gas - 1)
  }

  /** Node 646
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s646(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xc1;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s648(s4, gas - 1)
      else
        ExecuteFromCFGNode_s647(s4, gas - 1)
  }

  /** Node 647
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s647(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xc1;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s4, gas - 1)
  }

  /** Node 648
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s648(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xc1;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s671(s7, gas - 1)
      else
        ExecuteFromCFGNode_s649(s7, gas - 1)
  }

  /** Node 649
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s649(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xc1;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s667(s5, gas - 1)
      else
        ExecuteFromCFGNode_s650(s5, gas - 1)
  }

  /** Node 650
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s650(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xc1;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s651(s2, gas - 1)
  }

  /** Node 651
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s651(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xc1;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0xc1;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s653(s20, gas - 1)
      else
        ExecuteFromCFGNode_s652(s20, gas - 1)
  }

  /** Node 652
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s652(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0xc1;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s6, gas - 1)
  }

  /** Node 653
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s653(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0xc1;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s654(s6, gas - 1)
  }

  /** Node 654
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s654(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0xc1;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s655(s4, gas - 1)
  }

  /** Node 655
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s655(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xc1;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s662(s7, gas - 1)
      else
        ExecuteFromCFGNode_s656(s7, gas - 1)
  }

  /** Node 656
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s656(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0xc1;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s659(s9, gas - 1)
      else
        ExecuteFromCFGNode_s657(s9, gas - 1)
  }

  /** Node 657
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s657(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0xc1;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s658(s3, gas - 1)
  }

  /** Node 658
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s658(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0xc1;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0xc1;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 659
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s659(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xc1;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s661(s7, gas - 1)
      else
        ExecuteFromCFGNode_s660(s7, gas - 1)
  }

  /** Node 660
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s660(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xc1;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s661(s4, gas - 1)
  }

  /** Node 661
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s661(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xc1;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s655(s11, gas - 1)
  }

  /** Node 662
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s662(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0xc1;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s663(s8, gas - 1)
  }

  /** Node 663
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s663(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xc1;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s666(s10, gas - 1)
      else
        ExecuteFromCFGNode_s664(s10, gas - 1)
  }

  /** Node 664
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s664(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0xc1;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s665(s3, gas - 1)
  }

  /** Node 665
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s665(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0xc1;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0xc1;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 666
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s666(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xc1;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s8, gas - 1)
  }

  /** Node 667
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s667(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xc1;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s670(s7, gas - 1)
      else
        ExecuteFromCFGNode_s668(s7, gas - 1)
  }

  /** Node 668
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s668(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xc1;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s669(s3, gas - 1)
  }

  /** Node 669
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s669(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0xc1;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0xc1;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 670
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s670(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xc1;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s8, gas - 1)
  }

  /** Node 671
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s671(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0xc1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0xc1;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s7, gas - 1)
  }

  /** Node 672
    * Segment Id for this node is: 37
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s672(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup1(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push0(s8);
      var s10 := Dup1(s9);
      var s11 := MLoad(s10);
      var s12 := Push1(s11, 0x20);
      var s13 := Push2(s12, 0x0c69);
      var s14 := Dup4(s13);
      var s15 := CodeCopy(s14);
      var s16 := Dup2(s15);
      var s17 := MLoad(s16);
      var s18 := Swap2(s17);
      var s19 := MStore(s18);
      var s20 := SLoad(s19);
      var s21 := Push1(s20, 0x06);
      var s22 := SLoad(s21);
      var s23 := SelfBalance(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0270);
      var s28 := Swap1(s27);
      var s29 := Push1(s28, 0xff);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x0a);
      assert s31.Peek(2) == 0x270;
      var s32 := Push2(s31, 0x0adf);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s673(s33, gas - 1)
  }

  /** Node 673
    * Segment Id for this node is: 173
    * Starting at 0xadf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s673(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x270;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0aed);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0a41);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s674(s9, gas - 1)
  }

  /** Node 674
    * Segment Id for this node is: 156
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s674(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xaed

    requires s0.stack[6] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x270;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0a4f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s717(s5, gas - 1)
      else
        ExecuteFromCFGNode_s675(s5, gas - 1)
  }

  /** Node 675
    * Segment Id for this node is: 157
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s675(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x270;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s676(s4, gas - 1)
  }

  /** Node 676
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s676(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x270;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s677(s6, gas - 1)
  }

  /** Node 677
    * Segment Id for this node is: 174
    * Starting at 0xaed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s677(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x270;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s678(s7, gas - 1)
  }

  /** Node 678
    * Segment Id for this node is: 38
    * Starting at 0x270
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s678(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x270 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x027c);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0af4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s679(s8, gas - 1)
  }

  /** Node 679
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s679(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x27c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x27c;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x27c;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s682(s14, gas - 1)
      else
        ExecuteFromCFGNode_s680(s14, gas - 1)
  }

  /** Node 680
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s680(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x27c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x27c;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s681(s3, gas - 1)
  }

  /** Node 681
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s681(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x27c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x27c;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x27c;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 682
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s682(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x27c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x27c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s683(s6, gas - 1)
  }

  /** Node 683
    * Segment Id for this node is: 39
    * Starting at 0x27c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s683(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0286);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x09ec);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s684(s6, gas - 1)
  }

  /** Node 684
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s684(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x286

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x286;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s687(s10, gas - 1)
      else
        ExecuteFromCFGNode_s685(s10, gas - 1)
  }

  /** Node 685
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s685(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x286

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x286;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s686(s3, gas - 1)
  }

  /** Node 686
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s686(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x286

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x286;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x286;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 687
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s687(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x286

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x286;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s688(s6, gas - 1)
  }

  /** Node 688
    * Segment Id for this node is: 40
    * Starting at 0x286
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s688(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Push2(s4, 0x0293);
      var s6 := Dup3(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x09cd);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s689(s9, gas - 1)
  }

  /** Node 689
    * Segment Id for this node is: 143
    * Starting at 0x9cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s689(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x293

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x293;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09e7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s691(s5, gas - 1)
      else
        ExecuteFromCFGNode_s690(s5, gas - 1)
  }

  /** Node 690
    * Segment Id for this node is: 144
    * Starting at 0x9d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s690(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x293

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x293;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 691
    * Segment Id for this node is: 145
    * Starting at 0x9e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s691(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x293

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x293;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s692(s5, gas - 1)
  }

  /** Node 692
    * Segment Id for this node is: 41
    * Starting at 0x293
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s692(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Caller(s1);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Push1(s7, 0x20);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Dup2(s10);
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Swap2(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x02b1);
      var s19 := Swap1(s18);
      var s20 := Dup4(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x2b1;
      var s22 := Push2(s21, 0x0af4);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s693(s23, gas - 1)
  }

  /** Node 693
    * Segment Id for this node is: 175
    * Starting at 0xaf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s693(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x2b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2b1;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Dup2(s4);
      var s6 := IsZero(s5);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Div(s8);
      var s10 := Dup5(s9);
      var s11 := Eq(s10);
      assert s11.Peek(5) == 0x2b1;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x06d0);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s696(s14, gas - 1)
      else
        ExecuteFromCFGNode_s694(s14, gas - 1)
  }

  /** Node 694
    * Segment Id for this node is: 176
    * Starting at 0xb04
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s694(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x2b1;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s695(s3, gas - 1)
  }

  /** Node 695
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s695(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x2b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x2b1;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x2b1;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 696
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s696(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2b1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s697(s6, gas - 1)
  }

  /** Node 697
    * Segment Id for this node is: 42
    * Starting at 0x2b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s697(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Caller(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x1388);
      var s10 := Swap1(s9);
      var s11 := Dup4(s10);
      var s12 := Swap1(s11);
      var s13 := Push0(s12);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup2(s15);
      var s17 := Dup6(s16);
      var s18 := Dup9(s17);
      var s19 := Dup9(s18);
      var s20 := Call(s19);
      var s21 := Swap4(s20);
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := ReturnDataSize(s25);
      var s27 := Dup1(s26);
      var s28 := Push0(s27);
      var s29 := Dup2(s28);
      var s30 := Eq(s29);
      var s31 := Push2(s30, 0x02f6);
      assert s31.Peek(0) == 0x2f6;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s716(s32, gas - 1)
      else
        ExecuteFromCFGNode_s698(s32, gas - 1)
  }

  /** Node 698
    * Segment Id for this node is: 43
    * Starting at 0x2d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s698(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push0(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x02fb);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s699(s25, gas - 1)
  }

  /** Node 699
    * Segment Id for this node is: 45
    * Starting at 0x2fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s699(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Caller(s3);
      var s5 := Push0(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x02);
      var s10 := Push1(s9, 0x20);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := Dup3(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := Swap1(s16);
      var s18 := MLoad(s17);
      var s19 := Swap2(s18);
      var s20 := Swap4(s19);
      var s21 := Pop(s20);
      var s22 := Push0(s21);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Push2(s25, 0x0c89);
      var s27 := Dup4(s26);
      var s28 := CodeCopy(s27);
      var s29 := Dup2(s28);
      var s30 := MLoad(s29);
      var s31 := Swap2(s30);
      var s32 := MStore(s31);
      var s33 := Swap2(s32);
      var s34 := Push2(s33, 0x032d);
      var s35 := Swap2(s34);
      var s36 := Dup2(s35);
      var s37 := MStore(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Add(s38);
      var s40 := Swap1(s39);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s700(s41, gas - 1)
  }

  /** Node 700
    * Segment Id for this node is: 46
    * Starting at 0x32d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s700(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

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
      var s8 := Log3(s7);
      var s9 := Caller(s8);
      var s10 := Push0(s9);
      var s11 := Swap1(s10);
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x02);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup2(s17);
      var s19 := Keccak256(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      var s22 := Dup1(s21);
      var s23 := MStore(s22);
      var s24 := Push0(s23);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push2(s27, 0x0c69);
      var s29 := Dup4(s28);
      var s30 := CodeCopy(s29);
      var s31 := Dup2(s30);
      var s32 := MLoad(s31);
      var s33 := Swap2(s32);
      var s34 := MStore(s33);
      var s35 := Dup1(s34);
      var s36 := SLoad(s35);
      var s37 := Swap2(s36);
      var s38 := Swap3(s37);
      var s39 := Swap1(s38);
      var s40 := Swap2(s39);
      var s41 := Push2(s40, 0x0366);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s701(s41, gas - 1)
  }

  /** Node 701
    * Segment Id for this node is: 47
    * Starting at 0x35f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s701(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x366

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(1) == 0x366;
      var s2 := Dup5(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0x0b0b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s702(s5, gas - 1)
  }

  /** Node 702
    * Segment Id for this node is: 177
    * Starting at 0xb0b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s702(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x366

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x366;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s705(s10, gas - 1)
      else
        ExecuteFromCFGNode_s703(s10, gas - 1)
  }

  /** Node 703
    * Segment Id for this node is: 178
    * Starting at 0xb17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s703(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x366

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x366;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s704(s3, gas - 1)
  }

  /** Node 704
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s704(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x366

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x366;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x366;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 705
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s705(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x366

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x366;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s706(s6, gas - 1)
  }

  /** Node 706
    * Segment Id for this node is: 48
    * Starting at 0x366
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s706(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x366 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Caller(s6);
      var s8 := Push0(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x02);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup2(s15);
      var s17 := Keccak256(s16);
      var s18 := SStore(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := SLoad(s19);
      var s21 := Push2(s20, 0x0389);
      assert s21.Peek(0) == 0x389;
      var s22 := Swap1(s21);
      var s23 := Push1(s22, 0x33);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x09cd);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s707(s26, gas - 1)
  }

  /** Node 707
    * Segment Id for this node is: 143
    * Starting at 0x9cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s707(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x389

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x389;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x09e7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s709(s5, gas - 1)
      else
        ExecuteFromCFGNode_s708(s5, gas - 1)
  }

  /** Node 708
    * Segment Id for this node is: 144
    * Starting at 0x9d4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s708(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x389

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x389;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x12);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 709
    * Segment Id for this node is: 145
    * Starting at 0x9e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s709(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x389

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x389;
      var s2 := Pop(s1);
      var s3 := Div(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s710(s5, gas - 1)
  }

  /** Node 710
    * Segment Id for this node is: 49
    * Starting at 0x389
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s710(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0396);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x09ec);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s711(s8, gas - 1)
  }

  /** Node 711
    * Segment Id for this node is: 146
    * Starting at 0x9ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s711(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x396

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x396;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06d0);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s714(s10, gas - 1)
      else
        ExecuteFromCFGNode_s712(s10, gas - 1)
  }

  /** Node 712
    * Segment Id for this node is: 147
    * Starting at 0x9f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s712(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x396

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06d0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x396;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s713(s3, gas - 1)
  }

  /** Node 713
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s713(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x6d0

    requires s0.stack[4] == 0x396

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6d0;
      assert s1.Peek(4) == 0x396;
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
      assert s11.Peek(2) == 0x6d0;
      assert s11.Peek(6) == 0x396;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 714
    * Segment Id for this node is: 111
    * Starting at 0x6d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s714(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x396

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x396;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s715(s6, gas - 1)
  }

  /** Node 715
    * Segment Id for this node is: 50
    * Starting at 0x396
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s715(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := SStore(s2);
      var s4 := Stop(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 716
    * Segment Id for this node is: 44
    * Starting at 0x2f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s716(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s699(s4, gas - 1)
  }

  /** Node 717
    * Segment Id for this node is: 158
    * Starting at 0xa4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s717(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x270;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0a5b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s719(s4, gas - 1)
      else
        ExecuteFromCFGNode_s718(s4, gas - 1)
  }

  /** Node 718
    * Segment Id for this node is: 159
    * Starting at 0xa55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s718(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa55 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x270;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x06d0);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s676(s4, gas - 1)
  }

  /** Node 719
    * Segment Id for this node is: 160
    * Starting at 0xa5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s719(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x270;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0a71);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s742(s7, gas - 1)
      else
        ExecuteFromCFGNode_s720(s7, gas - 1)
  }

  /** Node 720
    * Segment Id for this node is: 161
    * Starting at 0xa65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s720(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x270;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0a7b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s738(s5, gas - 1)
      else
        ExecuteFromCFGNode_s721(s5, gas - 1)
  }

  /** Node 721
    * Segment Id for this node is: 162
    * Starting at 0xa6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s721(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a97);
      assert s1.Peek(0) == 0xa97;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x270;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s722(s2, gas - 1)
  }

  /** Node 722
    * Segment Id for this node is: 167
    * Starting at 0xa97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s722(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x270;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup4(s3);
      var s5 := Lt(s4);
      var s6 := Push2(s5, 0x0133);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x4e);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0xaed;
      assert s11.Peek(10) == 0x270;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0aba);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s724(s20, gas - 1)
      else
        ExecuteFromCFGNode_s723(s20, gas - 1)
  }

  /** Node 723
    * Segment Id for this node is: 168
    * Starting at 0xab2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s723(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xaed;
      assert s1.Peek(6) == 0x270;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x06d0);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s676(s6, gas - 1)
  }

  /** Node 724
    * Segment Id for this node is: 169
    * Starting at 0xaba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s724(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xaed

    requires s0.stack[7] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xaed;
      assert s1.Peek(7) == 0x270;
      var s2 := Push2(s1, 0x0ac4);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x09ff);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s725(s6, gas - 1)
  }

  /** Node 725
    * Segment Id for this node is: 148
    * Starting at 0x9ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s725(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xac4

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xac4;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x270;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s726(s4, gas - 1)
  }

  /** Node 726
    * Segment Id for this node is: 149
    * Starting at 0xa04
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s726(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa04 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x270;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a39);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s733(s7, gas - 1)
      else
        ExecuteFromCFGNode_s727(s7, gas - 1)
  }

  /** Node 727
    * Segment Id for this node is: 150
    * Starting at 0xa0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s727(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x270;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0a1f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s730(s9, gas - 1)
      else
        ExecuteFromCFGNode_s728(s9, gas - 1)
  }

  /** Node 728
    * Segment Id for this node is: 151
    * Starting at 0xa18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s728(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a1f);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x270;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s729(s3, gas - 1)
  }

  /** Node 729
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s729(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xa1f

    requires s0.stack[6] == 0xac4

    requires s0.stack[10] == 0xaed

    requires s0.stack[14] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa1f;
      assert s1.Peek(6) == 0xac4;
      assert s1.Peek(10) == 0xaed;
      assert s1.Peek(14) == 0x270;
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
      assert s11.Peek(2) == 0xa1f;
      assert s11.Peek(8) == 0xac4;
      assert s11.Peek(12) == 0xaed;
      assert s11.Peek(16) == 0x270;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 730
    * Segment Id for this node is: 152
    * Starting at 0xa1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s730(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x270;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a2c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s732(s7, gas - 1)
      else
        ExecuteFromCFGNode_s731(s7, gas - 1)
  }

  /** Node 731
    * Segment Id for this node is: 153
    * Starting at 0xa28
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s731(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x270;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s732(s4, gas - 1)
  }

  /** Node 732
    * Segment Id for this node is: 154
    * Starting at 0xa2c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s732(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x270;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0a04);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s726(s11, gas - 1)
  }

  /** Node 733
    * Segment Id for this node is: 155
    * Starting at 0xa39
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s733(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa39 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xac4

    requires s0.stack[9] == 0xaed

    requires s0.stack[13] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xac4;
      assert s1.Peek(9) == 0xaed;
      assert s1.Peek(13) == 0x270;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s734(s8, gas - 1)
  }

  /** Node 734
    * Segment Id for this node is: 170
    * Starting at 0xac4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s734(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x270;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ad7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s737(s10, gas - 1)
      else
        ExecuteFromCFGNode_s735(s10, gas - 1)
  }

  /** Node 735
    * Segment Id for this node is: 171
    * Starting at 0xad0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s735(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0ad7);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x270;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s736(s3, gas - 1)
  }

  /** Node 736
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s736(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xad7

    requires s0.stack[6] == 0xaed

    requires s0.stack[10] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad7;
      assert s1.Peek(6) == 0xaed;
      assert s1.Peek(10) == 0x270;
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
      assert s11.Peek(2) == 0xad7;
      assert s11.Peek(8) == 0xaed;
      assert s11.Peek(12) == 0x270;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 737
    * Segment Id for this node is: 172
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s737(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x270;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s677(s8, gas - 1)
  }

  /** Node 738
    * Segment Id for this node is: 164
    * Starting at 0xa7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s738(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x270;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a8c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s741(s7, gas - 1)
      else
        ExecuteFromCFGNode_s739(s7, gas - 1)
  }

  /** Node 739
    * Segment Id for this node is: 165
    * Starting at 0xa85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s739(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a8c);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x270;
      var s2 := Push2(s1, 0x09b9);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s740(s3, gas - 1)
  }

  /** Node 740
    * Segment Id for this node is: 142
    * Starting at 0x9b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s740(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xa8c

    requires s0.stack[5] == 0xaed

    requires s0.stack[9] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa8c;
      assert s1.Peek(5) == 0xaed;
      assert s1.Peek(9) == 0x270;
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
      assert s11.Peek(2) == 0xa8c;
      assert s11.Peek(7) == 0xaed;
      assert s11.Peek(11) == 0x270;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 741
    * Segment Id for this node is: 166
    * Starting at 0xa8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s741(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x270;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x06d0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s676(s8, gas - 1)
  }

  /** Node 742
    * Segment Id for this node is: 163
    * Starting at 0xa71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s742(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xaed

    requires s0.stack[8] == 0x270

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xaed;
      assert s1.Peek(8) == 0x270;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x06d0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s676(s7, gas - 1)
  }

  /** Node 743
    * Segment Id for this node is: 51
    * Starting at 0x39b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s743(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39b as nat
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
