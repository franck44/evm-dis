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
      var s7 := Push2(s6, 0x00c6);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s501(s8, gas - 1)
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
      var s6 := Push4(s5, 0x715018a6);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x007f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s289(s9, gas - 1)
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
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0059);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0228);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s5, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0250);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x027c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x029c);
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
    * Minimum capacity for this segment to prevent stack overflow: 2
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
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 8
    * Segment Id for this node is: 67
    * Starting at 0x29c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29c as nat
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
      var s5 := Push2(s4, 0x02a8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 68
    * Starting at 0x2a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a4 as nat
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
    * Segment Id for this node is: 69
    * Starting at 0x2a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0167);
      var s4 := Push2(s3, 0x02b7);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0d35);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 182
    * Starting at 0xd35
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd35 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2b7

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2b7;
      assert s1.Peek(3) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0d48);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s11, gas - 1)
      else
        ExecuteFromCFGNode_s12(s11, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 183
    * Starting at 0xd44
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2b7

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2b7;
      assert s1.Peek(6) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 13
    * Segment Id for this node is: 184
    * Starting at 0xd48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2b7

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2b7;
      assert s1.Peek(5) == 0x167;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0d53);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s7, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd53

    requires s0.stack[7] == 0x2b7

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd53;
      assert s1.Peek(7) == 0x2b7;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xd53;
      assert s11.Peek(9) == 0x2b7;
      assert s11.Peek(10) == 0x167;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s12, gas - 1)
      else
        ExecuteFromCFGNode_s15(s12, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd53

    requires s0.stack[7] == 0x2b7

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd53;
      assert s1.Peek(8) == 0x2b7;
      assert s1.Peek(9) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd53

    requires s0.stack[7] == 0x2b7

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd53;
      assert s1.Peek(7) == 0x2b7;
      assert s1.Peek(8) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s3, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 185
    * Starting at 0xd53
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2b7

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2b7;
      assert s1.Peek(6) == 0x167;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0d63);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0c8c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s11, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd63

    requires s0.stack[7] == 0x2b7

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd63;
      assert s1.Peek(7) == 0x2b7;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xd63;
      assert s11.Peek(9) == 0x2b7;
      assert s11.Peek(10) == 0x167;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s12, gas - 1)
      else
        ExecuteFromCFGNode_s19(s12, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd63

    requires s0.stack[7] == 0x2b7

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd63;
      assert s1.Peek(8) == 0x2b7;
      assert s1.Peek(9) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 20
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd63

    requires s0.stack[7] == 0x2b7

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd63;
      assert s1.Peek(7) == 0x2b7;
      assert s1.Peek(8) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 186
    * Starting at 0xd63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2b7

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2b7;
      assert s1.Peek(6) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s11, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 70
    * Starting at 0x2b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap2(s6);
      var s8 := Dup3(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x167;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x02);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x167;
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
      assert s31.Peek(4) == 0x167;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s36, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 35
    * Starting at 0x167
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
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
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0119);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 26
    * Starting at 0x119
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119 as nat
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

  /** Node 25
    * Segment Id for this node is: 63
    * Starting at 0x27c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27c as nat
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
      var s5 := Push2(s4, 0x0288);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s6, gas - 1)
      else
        ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 64
    * Starting at 0x284
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x284 as nat
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

  /** Node 27
    * Segment Id for this node is: 65
    * Starting at 0x288
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x288 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0142);
      var s4 := Push2(s3, 0x0297);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ca4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s8, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 169
    * Starting at 0xca4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x297

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x297;
      assert s1.Peek(3) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cb7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s11, gas - 1)
      else
        ExecuteFromCFGNode_s29(s11, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 170
    * Starting at 0xcb3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x297

    requires s0.stack[5] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x297;
      assert s1.Peek(6) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 30
    * Segment Id for this node is: 171
    * Starting at 0xcb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x297

    requires s0.stack[5] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x297;
      assert s1.Peek(5) == 0x142;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0cc2);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcc2

    requires s0.stack[7] == 0x297

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcc2;
      assert s1.Peek(7) == 0x297;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xcc2;
      assert s11.Peek(9) == 0x297;
      assert s11.Peek(10) == 0x142;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s12, gas - 1)
      else
        ExecuteFromCFGNode_s32(s12, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcc2

    requires s0.stack[7] == 0x297

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xcc2;
      assert s1.Peek(8) == 0x297;
      assert s1.Peek(9) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcc2

    requires s0.stack[7] == 0x297

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcc2;
      assert s1.Peek(7) == 0x297;
      assert s1.Peek(8) == 0x142;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s3, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 172
    * Starting at 0xcc2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x297

    requires s0.stack[6] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x297;
      assert s1.Peek(6) == 0x142;
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
      assert s11.Peek(1) == 0x297;
      assert s11.Peek(4) == 0x142;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s13, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 66
    * Starting at 0x297
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x297 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x142;
      var s2 := Push2(s1, 0x0617);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 107
    * Starting at 0x617
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x617 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02ef);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0749);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s8, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 115
    * Starting at 0x749
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x749 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x0787);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s6, gas - 1)
      else
        ExecuteFromCFGNode_s38(s6, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 116
    * Starting at 0x752
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x752 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 11, 0x16995c9bc8185b5bdd5b9d);
      var s19 := Push1(s18, 0xaa);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s28, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 83
    * Starting at 0x396
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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

  /** Node 40
    * Segment Id for this node is: 117
    * Starting at 0x787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x03);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Push2(s5, 0x07e4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s7, gas - 1)
      else
        ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 118
    * Starting at 0x792
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup5(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := And(s11);
      var s13 := Eq(s12);
      var s14 := Push2(s13, 0x07e4);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s15, gas - 1)
      else
        ExecuteFromCFGNode_s42(s15, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 119
    * Starting at 0x7a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x13);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 19, 0x151c98591a5b99c81b9bdd08195b98589b1959);
      var s19 := Push1(s18, 0x6a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s28, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 120
    * Starting at 0x7e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push1(s19, 0xff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x2ef;
      assert s21.Peek(8) == 0x142;
      var s22 := Dup1(s21);
      var s23 := Push2(s22, 0x0823);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s24, gas - 1)
      else
        ExecuteFromCFGNode_s44(s24, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 121
    * Starting at 0x806
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x806 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push1(s19, 0xff);
      var s21 := And(s20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s45(s21, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 122
    * Starting at 0x823
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x823 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0838);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s4, gas - 1)
      else
        ExecuteFromCFGNode_s46(s4, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 123
    * Starting at 0x829
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x829 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0833);
      assert s1.Peek(0) == 0x833;
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0b9d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s6, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 159
    * Starting at 0xb9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x833

    requires s0.stack[7] == 0x2ef

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x833;
      assert s1.Peek(7) == 0x2ef;
      assert s1.Peek(11) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x833;
      assert s11.Peek(10) == 0x2ef;
      assert s11.Peek(14) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup1(s18);
      var s20 := SLoad(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x833;
      assert s21.Peek(11) == 0x2ef;
      assert s21.Peek(15) == 0x142;
      var s22 := Swap3(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0bc5);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0e8e);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s29, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 216
    * Starting at 0xe8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xbc5

    requires s0.stack[9] == 0x833

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbc5;
      assert s1.Peek(9) == 0x833;
      assert s1.Peek(13) == 0x2ef;
      assert s1.Peek(17) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s10, gas - 1)
      else
        ExecuteFromCFGNode_s49(s10, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 217
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xbc5

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbc5;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s3, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0xbc5

    requires s0.stack[11] == 0x833

    requires s0.stack[15] == 0x2ef

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbc5;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0xbc5;
      assert s11.Peek(13) == 0x833;
      assert s11.Peek(17) == 0x2ef;
      assert s11.Peek(21) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 51
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xbc5

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbc5;
      assert s1.Peek(10) == 0x833;
      assert s1.Peek(14) == 0x2ef;
      assert s1.Peek(18) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 160
    * Starting at 0xbc5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x833

    requires s0.stack[11] == 0x2ef

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x833;
      assert s1.Peek(11) == 0x2ef;
      assert s1.Peek(15) == 0x142;
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
      assert s11.Peek(4) == 0x833;
      assert s11.Peek(8) == 0x2ef;
      assert s11.Peek(12) == 0x142;
      var s12 := Dup3(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x20);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(5) == 0x833;
      assert s21.Peek(9) == 0x2ef;
      assert s21.Peek(13) == 0x142;
      var s22 := Dup2(s21);
      var s23 := Keccak256(s22);
      var s24 := Dup1(s23);
      var s25 := SLoad(s24);
      var s26 := Dup4(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x0bf2);
      var s30 := Swap1(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(2) == 0xbf2;
      assert s31.Peek(9) == 0x833;
      assert s31.Peek(13) == 0x2ef;
      assert s31.Peek(17) == 0x142;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0ef3);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s34, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 222
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xbf2

    requires s0.stack[9] == 0x833

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbf2;
      assert s1.Peek(9) == 0x833;
      assert s1.Peek(13) == 0x2ef;
      assert s1.Peek(17) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s10, gas - 1)
      else
        ExecuteFromCFGNode_s54(s10, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 223
    * Starting at 0xeff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xbf2

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbf2;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s3, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0xbf2

    requires s0.stack[11] == 0x833

    requires s0.stack[15] == 0x2ef

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbf2;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0xbf2;
      assert s11.Peek(13) == 0x833;
      assert s11.Peek(17) == 0x2ef;
      assert s11.Peek(21) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 56
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xbf2

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbf2;
      assert s1.Peek(10) == 0x833;
      assert s1.Peek(14) == 0x2ef;
      assert s1.Peek(18) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s6, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 161
    * Starting at 0xbf2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x833

    requires s0.stack[11] == 0x2ef

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x833;
      assert s1.Peek(11) == 0x2ef;
      assert s1.Peek(15) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x833;
      assert s11.Peek(10) == 0x2ef;
      assert s11.Peek(14) == 0x142;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup4(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x833;
      assert s21.Peek(10) == 0x2ef;
      assert s21.Peek(14) == 0x142;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup4(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x073c);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x73c;
      assert s31.Peek(9) == 0x833;
      assert s31.Peek(13) == 0x2ef;
      assert s31.Peek(17) == 0x142;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s34, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 114
    * Starting at 0x73c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x833

    requires s0.stack[11] == 0x2ef

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x833;
      assert s1.Peek(11) == 0x2ef;
      assert s1.Peek(15) == 0x142;
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
      assert s11.Peek(0) == 0x833;
      assert s11.Peek(4) == 0x2ef;
      assert s11.Peek(8) == 0x142;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s12, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 124
    * Starting at 0x833
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x833 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 72
    * Starting at 0x2ef
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x142;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s61(s3, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s6, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 31
    * Starting at 0x142
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x142 as nat
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
      var s11 := Push2(s10, 0x0119);
      assert s11.Peek(0) == 0x119;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s12, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 125
    * Starting at 0x838
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x838 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x085d);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s18, gas - 1)
      else
        ExecuteFromCFGNode_s64(s18, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 126
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push2(s1, 0x0858);
      var s3 := Push2(s2, 0x02f9);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s4, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 74
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x858

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x858;
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0307);
      var s4 := Push1(s3, 0x09);
      var s5 := Push1(s4, 0x0a);
      var s6 := Push2(s5, 0x0e68);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s7, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 213
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x307

    requires s0.stack[4] == 0x858

    requires s0.stack[8] == 0x2ef

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x307;
      assert s1.Peek(4) == 0x858;
      assert s1.Peek(8) == 0x2ef;
      assert s1.Peek(12) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d2e);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0dc7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s9, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 196
    * Starting at 0xdc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xd2e

    requires s0.stack[6] == 0x307

    requires s0.stack[8] == 0x858

    requires s0.stack[12] == 0x2ef

    requires s0.stack[16] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x2ef;
      assert s1.Peek(16) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0dd6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s5, gas - 1)
      else
        ExecuteFromCFGNode_s68(s5, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 197
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x2ef;
      assert s1.Peek(16) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s4, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x2ef;
      assert s1.Peek(17) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s6, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x307

    requires s0.stack[6] == 0x858

    requires s0.stack[10] == 0x2ef

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(6) == 0x858;
      assert s1.Peek(10) == 0x2ef;
      assert s1.Peek(14) == 0x142;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s7, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 75
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x858

    requires s0.stack[6] == 0x2ef

    requires s0.stack[10] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x858;
      assert s1.Peek(6) == 0x2ef;
      assert s1.Peek(10) == 0x142;
      var s2 := Push2(s1, 0x0315);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x3b9aca00);
      var s5 := Push2(s4, 0x0e77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s6, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 214
    * Starting at 0xe77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x315

    requires s0.stack[4] == 0x858

    requires s0.stack[8] == 0x2ef

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x315;
      assert s1.Peek(4) == 0x858;
      assert s1.Peek(8) == 0x2ef;
      assert s1.Peek(12) == 0x142;
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
      assert s11.Peek(5) == 0x315;
      assert s11.Peek(7) == 0x858;
      assert s11.Peek(11) == 0x2ef;
      assert s11.Peek(15) == 0x142;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x02f3);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s14, gas - 1)
      else
        ExecuteFromCFGNode_s73(s14, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 215
    * Starting at 0xe87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x858

    requires s0.stack[9] == 0x2ef

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x858;
      assert s1.Peek(10) == 0x2ef;
      assert s1.Peek(14) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s3, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x315

    requires s0.stack[6] == 0x858

    requires s0.stack[10] == 0x2ef

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x858;
      assert s1.Peek(10) == 0x2ef;
      assert s1.Peek(14) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x315;
      assert s11.Peek(8) == 0x858;
      assert s11.Peek(12) == 0x2ef;
      assert s11.Peek(16) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 75
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x858

    requires s0.stack[9] == 0x2ef

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x315;
      assert s1.Peek(5) == 0x858;
      assert s1.Peek(9) == 0x2ef;
      assert s1.Peek(13) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s6, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 76
    * Starting at 0x315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x858

    requires s0.stack[6] == 0x2ef

    requires s0.stack[10] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x858;
      assert s1.Peek(6) == 0x2ef;
      assert s1.Peek(10) == 0x142;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s5, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 127
    * Starting at 0x858
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x858 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Eq(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s78(s4, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 128
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0918);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s4, gas - 1)
      else
        ExecuteFromCFGNode_s79(s4, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 129
    * Starting at 0x863
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x863 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup4(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x2ef;
      assert s11.Peek(8) == 0x142;
      var s12 := Push1(s11, 0x0c);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Swap1(s15);
      var s17 := Keccak256(s16);
      var s18 := SLoad(s17);
      var s19 := Push2(s18, 0x0886);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(2) == 0x886;
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
      var s22 := Push2(s21, 0x0ef3);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s23, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 222
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x886

    requires s0.stack[6] == 0x2ef

    requires s0.stack[10] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x886;
      assert s1.Peek(6) == 0x2ef;
      assert s1.Peek(10) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s10, gas - 1)
      else
        ExecuteFromCFGNode_s81(s10, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 223
    * Starting at 0xeff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x886

    requires s0.stack[7] == 0x2ef

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x886;
      assert s1.Peek(8) == 0x2ef;
      assert s1.Peek(12) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s3, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x886

    requires s0.stack[8] == 0x2ef

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x886;
      assert s1.Peek(8) == 0x2ef;
      assert s1.Peek(12) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x886;
      assert s11.Peek(10) == 0x2ef;
      assert s11.Peek(14) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 83
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x886

    requires s0.stack[7] == 0x2ef

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x886;
      assert s1.Peek(7) == 0x2ef;
      assert s1.Peek(11) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s6, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 130
    * Starting at 0x886
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x886 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Number(s1);
      var s3 := Lt(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08ac);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s7, gas - 1)
      else
        ExecuteFromCFGNode_s85(s7, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 131
    * Starting at 0x88f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0d);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Gt(s20);
      assert s21.Peek(4) == 0x2ef;
      assert s21.Peek(8) == 0x142;
      var s22 := IsZero(s21);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s86(s22, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 132
    * Starting at 0x8ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Push2(s1, 0x08ea);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s3, gas - 1)
      else
        ExecuteFromCFGNode_s87(s3, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 133
    * Starting at 0x8b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151e08185b5bdd5b9d081b1a5b5a5d);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s28, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 134
    * Starting at 0x8ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0d);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup1(s18);
      var s20 := SLoad(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x2ef;
      assert s21.Peek(11) == 0x142;
      var s22 := Swap3(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0912);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0e8e);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s29, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 216
    * Starting at 0xe8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x912

    requires s0.stack[9] == 0x2ef

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x912;
      assert s1.Peek(9) == 0x2ef;
      assert s1.Peek(13) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s10, gas - 1)
      else
        ExecuteFromCFGNode_s90(s10, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 217
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x912

    requires s0.stack[10] == 0x2ef

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x912;
      assert s1.Peek(11) == 0x2ef;
      assert s1.Peek(15) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s3, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x912

    requires s0.stack[11] == 0x2ef

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x912;
      assert s1.Peek(11) == 0x2ef;
      assert s1.Peek(15) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x912;
      assert s11.Peek(13) == 0x2ef;
      assert s11.Peek(17) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 92
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x912

    requires s0.stack[10] == 0x2ef

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x912;
      assert s1.Peek(10) == 0x2ef;
      assert s1.Peek(14) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s6, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 135
    * Starting at 0x912
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x912 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x2ef

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2ef;
      assert s1.Peek(11) == 0x142;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 136
    * Starting at 0x918
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x918 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0943);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s18, gas - 1)
      else
        ExecuteFromCFGNode_s95(s18, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 137
    * Starting at 0x930
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x930 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := IsZero(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s96(s15, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 138
    * Starting at 0x943
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x943 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x095b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s4, gas - 1)
      else
        ExecuteFromCFGNode_s97(s4, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 139
    * Starting at 0x949
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x949 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x09);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s14, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 140
    * Starting at 0x95b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2ef

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0a3e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s4, gas - 1)
      else
        ExecuteFromCFGNode_s99(s4, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 141
    * Starting at 0x961
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x961 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x09a4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s7, gas - 1)
      else
        ExecuteFromCFGNode_s100(s7, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 142
    * Starting at 0x96b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151e08185b5bdd5b9d081b1a5b5a5d);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s28, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 143
    * Starting at 0x9a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x09c7);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x9c7;
      assert s11.Peek(8) == 0x2ef;
      assert s11.Peek(12) == 0x142;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x20);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x9c7;
      assert s21.Peek(8) == 0x2ef;
      assert s21.Peek(12) == 0x142;
      var s22 := Keccak256(s21);
      var s23 := SLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s25, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 144
    * Starting at 0x9c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x2ef

    requires s0.stack[10] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2ef;
      assert s1.Peek(10) == 0x142;
      var s2 := Push2(s1, 0x09d1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0ef3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 222
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x9d1

    requires s0.stack[7] == 0x2ef

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9d1;
      assert s1.Peek(7) == 0x2ef;
      assert s1.Peek(11) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s10, gas - 1)
      else
        ExecuteFromCFGNode_s104(s10, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 223
    * Starting at 0xeff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9d1

    requires s0.stack[8] == 0x2ef

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x9d1;
      assert s1.Peek(9) == 0x2ef;
      assert s1.Peek(13) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s3, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x9d1

    requires s0.stack[9] == 0x2ef

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x9d1;
      assert s1.Peek(9) == 0x2ef;
      assert s1.Peek(13) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x9d1;
      assert s11.Peek(11) == 0x2ef;
      assert s11.Peek(15) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 106
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9d1

    requires s0.stack[8] == 0x2ef

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9d1;
      assert s1.Peek(8) == 0x2ef;
      assert s1.Peek(12) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s6, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 145
    * Starting at 0x9d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2ef

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2ef;
      assert s1.Peek(9) == 0x142;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0a15);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s5, gas - 1)
      else
        ExecuteFromCFGNode_s108(s5, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 146
    * Starting at 0x9d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x13);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 19, 0x15d85b1b195d08185b5bdd5b9d081b1a5b5a5d);
      var s19 := Push1(s18, 0x6a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s28, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 147
    * Starting at 0xa15
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0c);
      var s14 := Push1(s13, 0x20);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup4(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(7) == 0x2ef;
      assert s21.Peek(11) == 0x142;
      var s22 := Number(s21);
      var s23 := Swap1(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x0d);
      var s26 := Swap1(s25);
      var s27 := Swap2(s26);
      var s28 := MStore(s27);
      var s29 := Swap1(s28);
      var s30 := Keccak256(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(5) == 0x2ef;
      assert s31.Peek(9) == 0x142;
      var s32 := Swap1(s31);
      var s33 := SStore(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s110(s33, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 148
    * Starting at 0xa3e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push2(s1, 0x0833);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b9d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 198
    * Starting at 0xdd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x2ef;
      assert s1.Peek(17) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0de3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s4, gas - 1)
      else
        ExecuteFromCFGNode_s112(s4, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 199
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x2ef;
      assert s1.Peek(16) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s4, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 200
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x2ef;
      assert s1.Peek(17) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0df9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s7, gas - 1)
      else
        ExecuteFromCFGNode_s114(s7, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 201
    * Starting at 0xded
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e03);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s5, gas - 1)
      else
        ExecuteFromCFGNode_s115(s5, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 202
    * Starting at 0xdf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e1f);
      assert s1.Peek(0) == 0xe1f;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s2, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 207
    * Starting at 0xe1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x2ef;
      assert s1.Peek(18) == 0x142;
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
      assert s11.Peek(6) == 0xd2e;
      assert s11.Peek(10) == 0x307;
      assert s11.Peek(12) == 0x858;
      assert s11.Peek(16) == 0x2ef;
      assert s11.Peek(20) == 0x142;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0e42);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s20, gas - 1)
      else
        ExecuteFromCFGNode_s117(s20, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 208
    * Starting at 0xe3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x2ef;
      assert s1.Peek(16) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x02f3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s6, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 209
    * Starting at 0xe42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x2ef

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x2ef;
      assert s1.Peek(17) == 0x142;
      var s2 := Push2(s1, 0x0e4c);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0d84);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s6, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 188
    * Starting at 0xd84
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xe4c

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x858

    requires s0.stack[16] == 0x2ef

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe4c;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x858;
      assert s1.Peek(16) == 0x2ef;
      assert s1.Peek(20) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s4, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 189
    * Starting at 0xd89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x2ef;
      assert s1.Peek(23) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0dbf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s7, gas - 1)
      else
        ExecuteFromCFGNode_s121(s7, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 190
    * Starting at 0xd92
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x858;
      assert s1.Peek(20) == 0x2ef;
      assert s1.Peek(24) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0da5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s9, gas - 1)
      else
        ExecuteFromCFGNode_s122(s9, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 191
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da5);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x858;
      assert s1.Peek(20) == 0x2ef;
      assert s1.Peek(24) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[0] == 0xda5

    requires s0.stack[6] == 0xe4c

    requires s0.stack[10] == 0xd2e

    requires s0.stack[14] == 0x307

    requires s0.stack[16] == 0x858

    requires s0.stack[20] == 0x2ef

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x858;
      assert s1.Peek(20) == 0x2ef;
      assert s1.Peek(24) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xda5;
      assert s11.Peek(8) == 0xe4c;
      assert s11.Peek(12) == 0xd2e;
      assert s11.Peek(16) == 0x307;
      assert s11.Peek(18) == 0x858;
      assert s11.Peek(22) == 0x2ef;
      assert s11.Peek(26) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 124
    * Segment Id for this node is: 192
    * Starting at 0xda5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x2ef;
      assert s1.Peek(23) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0db2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s7, gas - 1)
      else
        ExecuteFromCFGNode_s125(s7, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 193
    * Starting at 0xdae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x2ef;
      assert s1.Peek(23) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s126(s4, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 194
    * Starting at 0xdb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x2ef;
      assert s1.Peek(23) == 0x142;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0d89);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s11, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 195
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x2ef

    requires s0.stack[23] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x2ef;
      assert s1.Peek(23) == 0x142;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s8, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 210
    * Starting at 0xe4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x2ef

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0e60);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s10, gas - 1)
      else
        ExecuteFromCFGNode_s129(s10, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 211
    * Starting at 0xe59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x2ef

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e60);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x858;
      assert s1.Peek(16) == 0x2ef;
      assert s1.Peek(20) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s3, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xe60

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x858

    requires s0.stack[16] == 0x2ef

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x858;
      assert s1.Peek(16) == 0x2ef;
      assert s1.Peek(20) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe60;
      assert s11.Peek(8) == 0xd2e;
      assert s11.Peek(12) == 0x307;
      assert s11.Peek(14) == 0x858;
      assert s11.Peek(18) == 0x2ef;
      assert s11.Peek(22) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 131
    * Segment Id for this node is: 212
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x2ef

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s8, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 204
    * Starting at 0xe03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x2ef;
      assert s1.Peek(18) == 0x142;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e14);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s7, gas - 1)
      else
        ExecuteFromCFGNode_s133(s7, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 205
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e14);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s3, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0xe14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x2ef

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x2ef;
      assert s1.Peek(19) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe14;
      assert s11.Peek(7) == 0xd2e;
      assert s11.Peek(11) == 0x307;
      assert s11.Peek(13) == 0x858;
      assert s11.Peek(17) == 0x2ef;
      assert s11.Peek(21) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 135
    * Segment Id for this node is: 206
    * Starting at 0xe14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x2ef;
      assert s1.Peek(18) == 0x142;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x02f3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s8, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 203
    * Starting at 0xdf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x2ef

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x2ef;
      assert s1.Peek(18) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x02f3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 60
    * Starting at 0x250
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x250 as nat
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
      var s5 := Push2(s4, 0x025c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s6, gas - 1)
      else
        ExecuteFromCFGNode_s138(s6, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 61
    * Starting at 0x258
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x258 as nat
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

  /** Node 139
    * Segment Id for this node is: 62
    * Starting at 0x25c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x03);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push3(s14, 0x626577);
      var s16 := Push1(s15, 0xe8);
      var s17 := Shl(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      var s22 := Push2(s21, 0x010c);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s23, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 25
    * Starting at 0x10c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0119);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0c3e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s8, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 162
    * Starting at 0xc3e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x119;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x119;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s142(s14, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 163
    * Starting at 0xc4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x119;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c6b);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s7, gas - 1)
      else
        ExecuteFromCFGNode_s143(s7, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 164
    * Starting at 0xc58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x119;
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
      assert s11.Peek(8) == 0x119;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0c4f);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s16, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 165
    * Starting at 0xc6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x119

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x119;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(7) == 0x119;
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
      assert s21.Peek(5) == 0x119;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s28, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 57
    * Starting at 0x228
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x228 as nat
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
      var s5 := Push2(s4, 0x0234);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s6, gas - 1)
      else
        ExecuteFromCFGNode_s146(s6, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 58
    * Starting at 0x230
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x230 as nat
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

  /** Node 147
    * Segment Id for this node is: 59
    * Starting at 0x234
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x234 as nat
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
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0119);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s20, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 8
    * Starting at 0x59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x715018a6);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x01e7);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s283(s6, gas - 1)
      else
        ExecuteFromCFGNode_s149(s6, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 9
    * Starting at 0x65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x751039fc);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01fe);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s5, gas - 1)
      else
        ExecuteFromCFGNode_s150(s5, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 10
    * Starting at 0x70
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8a8c523c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0213);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s5, gas - 1)
      else
        ExecuteFromCFGNode_s151(s5, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 11
    * Starting at 0x7b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
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

  /** Node 152
    * Segment Id for this node is: 54
    * Starting at 0x213
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
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
      var s5 := Push2(s4, 0x021f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s6, gas - 1)
      else
        ExecuteFromCFGNode_s153(s6, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 55
    * Starting at 0x21b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21b as nat
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

  /** Node 154
    * Segment Id for this node is: 56
    * Starting at 0x21f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x01fc);
      var s4 := Push2(s3, 0x042b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 90
    * Starting at 0x42b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x1fc;
      var s12 := Push2(s11, 0x0455);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s13, gas - 1)
      else
        ExecuteFromCFGNode_s156(s13, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 91
    * Starting at 0x43e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1fc;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0396);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x396;
      assert s11.Peek(2) == 0x1fc;
      var s12 := Push2(s11, 0x0ea1);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s13, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 218
    * Starting at 0xea1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x396

    requires s0.stack[2] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x396;
      assert s1.Peek(2) == 0x1fc;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Dup2(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push32(s9, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x396;
      assert s11.Peek(4) == 0x1fc;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s18, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 83
    * Starting at 0x396
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1fc;
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

  /** Node 159
    * Segment Id for this node is: 92
    * Starting at 0x455
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x455 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push1(s1, 0x03);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x049a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s8, gas - 1)
      else
        ExecuteFromCFGNode_s160(s8, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 93
    * Starting at 0x461
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x461 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1fc;
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
      assert s11.Peek(3) == 0x1fc;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x105b1c9958591e48195b98589b1959);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(3) == 0x1fc;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s28, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 94
    * Starting at 0x49a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push1(s1, 0x03);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0xff);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Or(s8);
      var s10 := Swap1(s9);
      var s11 := SStore(s10);
      assert s11.Peek(0) == 0x1fc;
      var s12 := Push1(s11, 0x08);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0x06);
      var s15 := Dup1(s14);
      var s16 := SLoad(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(4) == 0x1fc;
      var s22 := Not(s21);
      var s23 := And(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0xa0);
      var s27 := Shl(s26);
      var s28 := Sub(s27);
      var s29 := Swap1(s28);
      var s30 := Swap3(s29);
      var s31 := And(s30);
      assert s31.Peek(3) == 0x1fc;
      var s32 := Swap2(s31);
      var s33 := Dup3(s32);
      var s34 := Or(s33);
      var s35 := Swap1(s34);
      var s36 := SStore(s35);
      var s37 := Push1(s36, 0x40);
      var s38 := Dup1(s37);
      var s39 := MLoad(s38);
      var s40 := Push4(s39, 0xc45a0155);
      var s41 := Push1(s40, 0xe0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s162(s41, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 95
    * Starting at 0x4d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Shl(s0);
      assert s1.Peek(4) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := MLoad(s4);
      var s6 := Push2(s5, 0x05b3);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Push4(s8, 0xc45a0155);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x04);
      assert s11.Peek(5) == 0x5b3;
      assert s11.Peek(6) == 0x1fc;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Swap3(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Swap3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Dup3(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(8) == 0x5b3;
      assert s21.Peek(9) == 0x1fc;
      var s22 := Sub(s21);
      var s23 := Add(s22);
      var s24 := Dup2(s23);
      var s25 := Dup7(s24);
      var s26 := Gas(s25);
      var s27 := StaticCall(s26);
      var s28 := IsZero(s27);
      var s29 := Dup1(s28);
      var s30 := IsZero(s29);
      var s31 := Push2(s30, 0x0507);
      assert s31.Peek(0) == 0x507;
      assert s31.Peek(6) == 0x5b3;
      assert s31.Peek(7) == 0x1fc;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s32, gas - 1)
      else
        ExecuteFromCFGNode_s163(s32, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 96
    * Starting at 0x4fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x5b3

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x5b3;
      assert s1.Peek(6) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 164
    * Segment Id for this node is: 97
    * Starting at 0x507
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x507 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x5b3

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5b3;
      assert s1.Peek(5) == 0x1fc;
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
      assert s11.Peek(4) == 0x5b3;
      assert s11.Peek(5) == 0x1fc;
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
      assert s21.Peek(3) == 0x5b3;
      assert s21.Peek(4) == 0x1fc;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x052b);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0ed6);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s28, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 219
    * Starting at 0xed6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x52b

    requires s0.stack[3] == 0x5b3

    requires s0.stack[4] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x52b;
      assert s1.Peek(3) == 0x5b3;
      assert s1.Peek(4) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ee8);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s10, gas - 1)
      else
        ExecuteFromCFGNode_s166(s10, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 220
    * Starting at 0xee4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x52b

    requires s0.stack[4] == 0x5b3

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x52b;
      assert s1.Peek(5) == 0x5b3;
      assert s1.Peek(6) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 167
    * Segment Id for this node is: 221
    * Starting at 0xee8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x52b

    requires s0.stack[4] == 0x5b3

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x52b;
      assert s1.Peek(4) == 0x5b3;
      assert s1.Peek(5) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0d2e);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s7, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x52b

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2e;
      assert s1.Peek(6) == 0x52b;
      assert s1.Peek(7) == 0x5b3;
      assert s1.Peek(8) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xd2e;
      assert s11.Peek(8) == 0x52b;
      assert s11.Peek(9) == 0x5b3;
      assert s11.Peek(10) == 0x1fc;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s12, gas - 1)
      else
        ExecuteFromCFGNode_s169(s12, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x52b

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(7) == 0x52b;
      assert s1.Peek(8) == 0x5b3;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 170
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x52b

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2e;
      assert s1.Peek(6) == 0x52b;
      assert s1.Peek(7) == 0x5b3;
      assert s1.Peek(8) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s3, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x52b

    requires s0.stack[5] == 0x5b3

    requires s0.stack[6] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x52b;
      assert s1.Peek(5) == 0x5b3;
      assert s1.Peek(6) == 0x1fc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s7, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 98
    * Starting at 0x52b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x5b3

    requires s0.stack[2] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b3;
      assert s1.Peek(2) == 0x1fc;
      var s2 := Push2(s1, 0x05ae);
      var s3 := Address(s2);
      var s4 := Push1(s3, 0x06);
      var s5 := Push1(s4, 0x00);
      var s6 := Swap1(s5);
      var s7 := SLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x5ae;
      assert s11.Peek(5) == 0x5b3;
      assert s11.Peek(6) == 0x1fc;
      var s12 := Div(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := And(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(5) == 0x5ae;
      assert s21.Peek(7) == 0x5b3;
      assert s21.Peek(8) == 0x1fc;
      var s22 := Shl(s21);
      var s23 := Sub(s22);
      var s24 := And(s23);
      var s25 := Push4(s24, 0x4aa4a4fc);
      var s26 := Push1(s25, 0x40);
      var s27 := MLoad(s26);
      var s28 := Dup2(s27);
      var s29 := Push4(s28, 0xffffffff);
      var s30 := And(s29);
      var s31 := Push1(s30, 0xe0);
      assert s31.Peek(6) == 0x5ae;
      assert s31.Peek(8) == 0x5b3;
      assert s31.Peek(9) == 0x1fc;
      var s32 := Shl(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x04);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Dup1(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s173(s41, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 99
    * Starting at 0x56d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x5ae

    requires s0.stack[10] == 0x5b3

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(7) == 0x5ae;
      assert s1.Peek(9) == 0x5b3;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Gas(s3);
      var s5 := StaticCall(s4);
      var s6 := IsZero(s5);
      var s7 := Dup1(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0582);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s10, gas - 1)
      else
        ExecuteFromCFGNode_s174(s10, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 100
    * Starting at 0x579
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x579 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x5ae

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x5ae;
      assert s1.Peek(8) == 0x5b3;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 175
    * Segment Id for this node is: 101
    * Starting at 0x582
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x582 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x5ae

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5ae;
      assert s1.Peek(7) == 0x5b3;
      assert s1.Peek(8) == 0x1fc;
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
      assert s11.Peek(5) == 0x5ae;
      assert s11.Peek(7) == 0x5b3;
      assert s11.Peek(8) == 0x1fc;
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
      assert s21.Peek(4) == 0x5ae;
      assert s21.Peek(6) == 0x5b3;
      assert s21.Peek(7) == 0x1fc;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x05a6);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0ed6);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s28, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 219
    * Starting at 0xed6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x5a6

    requires s0.stack[4] == 0x5ae

    requires s0.stack[6] == 0x5b3

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5a6;
      assert s1.Peek(4) == 0x5ae;
      assert s1.Peek(6) == 0x5b3;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ee8);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s10, gas - 1)
      else
        ExecuteFromCFGNode_s177(s10, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 220
    * Starting at 0xee4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x5ae

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x5a6;
      assert s1.Peek(6) == 0x5ae;
      assert s1.Peek(8) == 0x5b3;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 178
    * Segment Id for this node is: 221
    * Starting at 0xee8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5a6

    requires s0.stack[5] == 0x5ae

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5a6;
      assert s1.Peek(5) == 0x5ae;
      assert s1.Peek(7) == 0x5b3;
      assert s1.Peek(8) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0d2e);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s7, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x5ae

    requires s0.stack[10] == 0x5b3

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2e;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x5ae;
      assert s1.Peek(10) == 0x5b3;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xd2e;
      assert s11.Peek(8) == 0x5a6;
      assert s11.Peek(10) == 0x5ae;
      assert s11.Peek(12) == 0x5b3;
      assert s11.Peek(13) == 0x1fc;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s181(s12, gas - 1)
      else
        ExecuteFromCFGNode_s180(s12, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x5ae

    requires s0.stack[10] == 0x5b3

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(7) == 0x5a6;
      assert s1.Peek(9) == 0x5ae;
      assert s1.Peek(11) == 0x5b3;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 181
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x5a6

    requires s0.stack[8] == 0x5ae

    requires s0.stack[10] == 0x5b3

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2e;
      assert s1.Peek(6) == 0x5a6;
      assert s1.Peek(8) == 0x5ae;
      assert s1.Peek(10) == 0x5b3;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s3, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5a6

    requires s0.stack[6] == 0x5ae

    requires s0.stack[8] == 0x5b3

    requires s0.stack[9] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5a6;
      assert s1.Peek(6) == 0x5ae;
      assert s1.Peek(8) == 0x5b3;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s7, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 102
    * Starting at 0x5a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x5ae

    requires s0.stack[4] == 0x5b3

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5ae;
      assert s1.Peek(4) == 0x5b3;
      assert s1.Peek(5) == 0x1fc;
      var s2 := Push2(s1, 0x2710);
      var s3 := Push2(s2, 0x0a49);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s4, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 149
    * Starting at 0xa49
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa49 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x5ae

    requires s0.stack[5] == 0x5b3

    requires s0.stack[6] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ae;
      assert s1.Peek(5) == 0x5b3;
      assert s1.Peek(6) == 0x1fc;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup1(s10);
      assert s11.Peek(7) == 0x5ae;
      assert s11.Peek(9) == 0x5b3;
      assert s11.Peek(10) == 0x1fc;
      var s12 := Dup3(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Dup2(s16);
      var s18 := Swap1(s17);
      var s19 := MStore(s18);
      var s20 := Swap2(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x5ae;
      assert s21.Peek(9) == 0x5b3;
      assert s21.Peek(10) == 0x1fc;
      var s22 := Add(s21);
      var s23 := Swap2(s22);
      var s24 := Swap1(s23);
      var s25 := Swap2(s24);
      var s26 := MStore(s25);
      var s27 := Dup3(s26);
      var s28 := Push1(s27, 0x01);
      var s29 := Push1(s28, 0x01);
      var s30 := Push1(s29, 0xa0);
      var s31 := Shl(s30);
      assert s31.Peek(7) == 0x5ae;
      assert s31.Peek(9) == 0x5b3;
      assert s31.Peek(10) == 0x1fc;
      var s32 := Sub(s31);
      var s33 := And(s32);
      var s34 := Dup5(s33);
      var s35 := Push1(s34, 0x01);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0xa0);
      var s38 := Shl(s37);
      var s39 := Sub(s38);
      var s40 := And(s39);
      var s41 := Gt(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s185(s41, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 150
    * Starting at 0xa7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x5ae

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := IsZero(s0);
      assert s1.Peek(5) == 0x5ae;
      assert s1.Peek(7) == 0x5b3;
      assert s1.Peek(8) == 0x1fc;
      var s2 := Push2(s1, 0x0a84);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s3, gas - 1)
      else
        ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 151
    * Starting at 0xa81
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x5ae

    requires s0.stack[6] == 0x5b3

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(4) == 0x5ae;
      assert s1.Peek(6) == 0x5b3;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s187(s3, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 152
    * Starting at 0xa84
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x5ae

    requires s0.stack[6] == 0x5b3

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ae;
      assert s1.Peek(6) == 0x5b3;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Dup3(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x5ae;
      assert s11.Peek(8) == 0x5b3;
      assert s11.Peek(9) == 0x1fc;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Swap5(s15);
      var s17 := Dup6(s16);
      var s18 := And(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(5) == 0x5ae;
      assert s21.Peek(7) == 0x5b3;
      assert s21.Peek(8) == 0x1fc;
      var s22 := Swap1(s21);
      var s23 := Swap4(s22);
      var s24 := And(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Dup4(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := Push3(s28, 0xffffff);
      var s30 := And(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(3) == 0x5ae;
      assert s31.Peek(5) == 0x5b3;
      assert s31.Peek(6) == 0x1fc;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Swap2(s33);
      var s35 := Swap1(s34);
      var s36 := Swap2(s35);
      var s37 := MStore(s36);
      var s38 := Swap1(s37);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s39, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 103
    * Starting at 0x5ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x5b3

    requires s0.stack[3] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5b3;
      assert s1.Peek(3) == 0x1fc;
      var s2 := Push2(s1, 0x0ab4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s3, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 153
    * Starting at 0xab4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x5b3

    requires s0.stack[3] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5b3;
      assert s1.Peek(3) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x5b3;
      assert s11.Peek(6) == 0x1fc;
      var s12 := And(s11);
      var s13 := Dup3(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Add(s14);
      var s16 := MLoad(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x5b3;
      assert s21.Peek(7) == 0x1fc;
      var s22 := And(s21);
      var s23 := Lt(s22);
      var s24 := Push2(s23, 0x0adc);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s25, gas - 1)
      else
        ExecuteFromCFGNode_s190(s25, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 154
    * Starting at 0xad8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5b3

    requires s0.stack[4] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x5b3;
      assert s1.Peek(5) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 191
    * Segment Id for this node is: 155
    * Starting at 0xadc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5b3

    requires s0.stack[4] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b3;
      assert s1.Peek(4) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Dup1(s9);
      var s11 := Dup7(s10);
      assert s11.Peek(9) == 0x5b3;
      assert s11.Peek(10) == 0x1fc;
      var s12 := Add(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := MLoad(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Swap6(s20);
      assert s21.Peek(10) == 0x5b3;
      assert s21.Peek(11) == 0x1fc;
      var s22 := Dup7(s21);
      var s23 := And(s22);
      var s24 := Dup2(s23);
      var s25 := Dup7(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Swap5(s27);
      var s29 := Swap1(s28);
      var s30 := Swap3(s29);
      var s31 := And(s30);
      assert s31.Peek(8) == 0x5b3;
      assert s31.Peek(9) == 0x1fc;
      var s32 := Dup5(s31);
      var s33 := Dup3(s32);
      var s34 := Add(s33);
      var s35 := MStore(s34);
      var s36 := Push3(s35, 0xffffff);
      var s37 := Swap1(s36);
      var s38 := Swap2(s37);
      var s39 := And(s38);
      var s40 := Push1(s39, 0x60);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s192(s41, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 156
    * Starting at 0xb0e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x5b3

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(10) == 0x5b3;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Add(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := MStore(s5);
      var s7 := Dup2(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup6(s9);
      var s11 := Sub(s10);
      assert s11.Peek(9) == 0x5b3;
      assert s11.Peek(10) == 0x1fc;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x80);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Swap1(s18);
      var s20 := Swap3(s19);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0x5b3;
      assert s21.Peek(8) == 0x1fc;
      var s22 := Dup2(s21);
      var s23 := MLoad(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Swap3(s25);
      var s27 := Add(s26);
      var s28 := Keccak256(s27);
      var s29 := Push1(s28, 0x01);
      var s30 := Push1(s29, 0x01);
      var s31 := Push1(s30, 0xf8);
      assert s31.Peek(9) == 0x5b3;
      assert s31.Peek(10) == 0x1fc;
      var s32 := Shl(s31);
      var s33 := Sub(s32);
      var s34 := Not(s33);
      var s35 := Push1(s34, 0xa0);
      var s36 := Dup5(s35);
      var s37 := Add(s36);
      var s38 := MStore(s37);
      var s39 := Swap1(s38);
      var s40 := Dup6(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s193(s41, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 157
    * Starting at 0xb3c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5b3

    requires s0.stack[8] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Shl(s0);
      assert s1.Peek(6) == 0x5b3;
      assert s1.Peek(7) == 0x1fc;
      var s2 := PushN(s1, 12, 0xffffffffffffffffffffffff);
      var s3 := Not(s2);
      var s4 := And(s3);
      var s5 := Push1(s4, 0xa1);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0xb5);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x5b3;
      assert s11.Peek(7) == 0x1fc;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54);
      var s14 := Push1(s13, 0xd5);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0xf5);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Dup1(s20);
      assert s21.Peek(6) == 0x5b3;
      assert s21.Peek(7) == 0x1fc;
      var s22 := MLoad(s21);
      var s23 := Push1(s22, 0x1f);
      var s24 := Not(s23);
      var s25 := Dup2(s24);
      var s26 := Dup5(s25);
      var s27 := Sub(s26);
      var s28 := Add(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(6) == 0x5b3;
      assert s31.Peek(7) == 0x1fc;
      var s32 := Swap1(s31);
      var s33 := MStore(s32);
      var s34 := Dup1(s33);
      var s35 := MLoad(s34);
      var s36 := Push1(s35, 0x20);
      var s37 := Swap1(s36);
      var s38 := Swap2(s37);
      var s39 := Add(s38);
      var s40 := Keccak256(s39);
      var s41 := Swap4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s194(s41, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 158
    * Starting at 0xb98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x5b3

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap3(s0);
      assert s1.Peek(3) == 0x5b3;
      assert s1.Peek(5) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s5, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 104
    * Starting at 0x5b3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1fc;
      var s2 := Push1(s1, 0x07);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Not(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0x1fc;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Swap3(s16);
      var s18 := Swap1(s17);
      var s19 := Swap3(s18);
      var s20 := And(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(3) == 0x1fc;
      var s22 := Dup3(s21);
      var s23 := Or(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Push2(s25, 0x0615);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s27, gas - 1)
      else
        ExecuteFromCFGNode_s196(s27, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 105
    * Starting at 0x5d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1fc;
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
      assert s11.Peek(3) == 0x1fc;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x14);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push20(s17, 0x496e76616c696420706169722061646472657373);
      var s19 := Push1(s18, 0x60);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(3) == 0x1fc;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s28, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 106
    * Starting at 0x615
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x615 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s2, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 50
    * Starting at 0x1fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fc as nat
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

  /** Node 199
    * Segment Id for this node is: 51
    * Starting at 0x1fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fe as nat
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
      var s5 := Push2(s4, 0x020a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s6, gas - 1)
      else
        ExecuteFromCFGNode_s200(s6, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 52
    * Starting at 0x206
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x206 as nat
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

  /** Node 201
    * Segment Id for this node is: 53
    * Starting at 0x20a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x01fc);
      var s4 := Push2(s3, 0x03e9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s5, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 85
    * Starting at 0x3e9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x1fc;
      var s12 := Push2(s11, 0x0413);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s13, gas - 1)
      else
        ExecuteFromCFGNode_s203(s13, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 86
    * Starting at 0x3fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1fc;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0396);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x396;
      assert s11.Peek(2) == 0x1fc;
      var s12 := Push2(s11, 0x0ea1);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s13, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 87
    * Starting at 0x413
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x413 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push2(s1, 0x041b);
      var s3 := Push2(s2, 0x02f9);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s4, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 74
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x41b

    requires s0.stack[1] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x41b;
      assert s1.Peek(1) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0307);
      var s4 := Push1(s3, 0x09);
      var s5 := Push1(s4, 0x0a);
      var s6 := Push2(s5, 0x0e68);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s7, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 213
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x307

    requires s0.stack[4] == 0x41b

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x307;
      assert s1.Peek(4) == 0x41b;
      assert s1.Peek(5) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d2e);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0dc7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s9, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 196
    * Starting at 0xdc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xd2e

    requires s0.stack[6] == 0x307

    requires s0.stack[8] == 0x41b

    requires s0.stack[9] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x41b;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0dd6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s5, gas - 1)
      else
        ExecuteFromCFGNode_s208(s5, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 197
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x41b;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s4, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x41b;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s6, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x307

    requires s0.stack[6] == 0x41b

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(6) == 0x41b;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s7, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 75
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x41b

    requires s0.stack[3] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x41b;
      assert s1.Peek(3) == 0x1fc;
      var s2 := Push2(s1, 0x0315);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x3b9aca00);
      var s5 := Push2(s4, 0x0e77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s6, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 214
    * Starting at 0xe77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x315

    requires s0.stack[4] == 0x41b

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x315;
      assert s1.Peek(4) == 0x41b;
      assert s1.Peek(5) == 0x1fc;
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
      assert s11.Peek(5) == 0x315;
      assert s11.Peek(7) == 0x41b;
      assert s11.Peek(8) == 0x1fc;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x02f3);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s14, gas - 1)
      else
        ExecuteFromCFGNode_s213(s14, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 215
    * Starting at 0xe87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x41b

    requires s0.stack[6] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x41b;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s3, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x315

    requires s0.stack[6] == 0x41b

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x41b;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x315;
      assert s11.Peek(8) == 0x41b;
      assert s11.Peek(9) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 215
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x41b

    requires s0.stack[6] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x315;
      assert s1.Peek(5) == 0x41b;
      assert s1.Peek(6) == 0x1fc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s6, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 76
    * Starting at 0x315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x41b

    requires s0.stack[3] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x41b;
      assert s1.Peek(3) == 0x1fc;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s5, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 88
    * Starting at 0x41b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1fc;
      var s2 := Push1(s1, 0x04);
      var s3 := SStore(s2);
      var s4 := Push2(s3, 0x0426);
      var s5 := Push2(s4, 0x02f9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s6, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 74
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x426

    requires s0.stack[1] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x426;
      assert s1.Peek(1) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0307);
      var s4 := Push1(s3, 0x09);
      var s5 := Push1(s4, 0x0a);
      var s6 := Push2(s5, 0x0e68);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s7, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 213
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x307

    requires s0.stack[4] == 0x426

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x307;
      assert s1.Peek(4) == 0x426;
      assert s1.Peek(5) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d2e);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0dc7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s9, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 196
    * Starting at 0xdc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xd2e

    requires s0.stack[6] == 0x307

    requires s0.stack[8] == 0x426

    requires s0.stack[9] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x426;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0dd6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s5, gas - 1)
      else
        ExecuteFromCFGNode_s221(s5, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 197
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x426;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s4, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x426;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s6, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x307

    requires s0.stack[6] == 0x426

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(6) == 0x426;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s7, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 75
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x426

    requires s0.stack[3] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x426;
      assert s1.Peek(3) == 0x1fc;
      var s2 := Push2(s1, 0x0315);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x3b9aca00);
      var s5 := Push2(s4, 0x0e77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s6, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 214
    * Starting at 0xe77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x315

    requires s0.stack[4] == 0x426

    requires s0.stack[5] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x315;
      assert s1.Peek(4) == 0x426;
      assert s1.Peek(5) == 0x1fc;
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
      assert s11.Peek(5) == 0x315;
      assert s11.Peek(7) == 0x426;
      assert s11.Peek(8) == 0x1fc;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x02f3);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s14, gas - 1)
      else
        ExecuteFromCFGNode_s226(s14, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 215
    * Starting at 0xe87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x426

    requires s0.stack[6] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x426;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s3, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x315

    requires s0.stack[6] == 0x426

    requires s0.stack[7] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x426;
      assert s1.Peek(7) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x315;
      assert s11.Peek(8) == 0x426;
      assert s11.Peek(9) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 228
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x426

    requires s0.stack[6] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x315;
      assert s1.Peek(5) == 0x426;
      assert s1.Peek(6) == 0x1fc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s6, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 76
    * Starting at 0x315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x426

    requires s0.stack[3] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x426;
      assert s1.Peek(3) == 0x1fc;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s5, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 89
    * Starting at 0x426
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x426 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1fc;
      var s2 := Push1(s1, 0x05);
      var s3 := SStore(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s4, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 198
    * Starting at 0xdd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x426;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0de3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s4, gas - 1)
      else
        ExecuteFromCFGNode_s232(s4, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 199
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x426;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s4, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 200
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x426;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0df9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s256(s7, gas - 1)
      else
        ExecuteFromCFGNode_s234(s7, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 201
    * Starting at 0xded
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x426;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e03);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s5, gas - 1)
      else
        ExecuteFromCFGNode_s235(s5, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 202
    * Starting at 0xdf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e1f);
      assert s1.Peek(0) == 0xe1f;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x426;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s2, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 207
    * Starting at 0xe1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x426;
      assert s1.Peek(11) == 0x1fc;
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
      assert s11.Peek(6) == 0xd2e;
      assert s11.Peek(10) == 0x307;
      assert s11.Peek(12) == 0x426;
      assert s11.Peek(13) == 0x1fc;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0e42);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s20, gas - 1)
      else
        ExecuteFromCFGNode_s237(s20, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 208
    * Starting at 0xe3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x426;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x02f3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s6, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 209
    * Starting at 0xe42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x426

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x426;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Push2(s1, 0x0e4c);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0d84);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s6, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 188
    * Starting at 0xd84
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xe4c

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x426

    requires s0.stack[13] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe4c;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x426;
      assert s1.Peek(13) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s240(s4, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 189
    * Starting at 0xd89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x426;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0dbf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s7, gas - 1)
      else
        ExecuteFromCFGNode_s241(s7, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 190
    * Starting at 0xd92
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x426;
      assert s1.Peek(17) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0da5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s9, gas - 1)
      else
        ExecuteFromCFGNode_s242(s9, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 191
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da5);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x426;
      assert s1.Peek(17) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s3, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xda5

    requires s0.stack[6] == 0xe4c

    requires s0.stack[10] == 0xd2e

    requires s0.stack[14] == 0x307

    requires s0.stack[16] == 0x426

    requires s0.stack[17] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x426;
      assert s1.Peek(17) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xda5;
      assert s11.Peek(8) == 0xe4c;
      assert s11.Peek(12) == 0xd2e;
      assert s11.Peek(16) == 0x307;
      assert s11.Peek(18) == 0x426;
      assert s11.Peek(19) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 244
    * Segment Id for this node is: 192
    * Starting at 0xda5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x426;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0db2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s7, gas - 1)
      else
        ExecuteFromCFGNode_s245(s7, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 193
    * Starting at 0xdae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x426;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s246(s4, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 194
    * Starting at 0xdb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x426;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0d89);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s11, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 195
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x426

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x426;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s8, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 210
    * Starting at 0xe4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x426

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x426;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0e60);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s10, gas - 1)
      else
        ExecuteFromCFGNode_s249(s10, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 211
    * Starting at 0xe59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x426

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e60);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x426;
      assert s1.Peek(13) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s3, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xe60

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x426

    requires s0.stack[13] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x426;
      assert s1.Peek(13) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe60;
      assert s11.Peek(8) == 0xd2e;
      assert s11.Peek(12) == 0x307;
      assert s11.Peek(14) == 0x426;
      assert s11.Peek(15) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 251
    * Segment Id for this node is: 212
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x426

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x426;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s8, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 204
    * Starting at 0xe03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x426;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e14);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s7, gas - 1)
      else
        ExecuteFromCFGNode_s253(s7, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 205
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e14);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x426;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s3, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xe14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x426

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x426;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe14;
      assert s11.Peek(7) == 0xd2e;
      assert s11.Peek(11) == 0x307;
      assert s11.Peek(13) == 0x426;
      assert s11.Peek(14) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 255
    * Segment Id for this node is: 206
    * Starting at 0xe14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x426;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x02f3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s8, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 203
    * Starting at 0xdf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x426

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x426;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x02f3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s7, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 198
    * Starting at 0xdd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x41b;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0de3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s4, gas - 1)
      else
        ExecuteFromCFGNode_s258(s4, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 199
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x41b;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s4, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 200
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x41b;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0df9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s7, gas - 1)
      else
        ExecuteFromCFGNode_s260(s7, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 201
    * Starting at 0xded
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x41b;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e03);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s5, gas - 1)
      else
        ExecuteFromCFGNode_s261(s5, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 202
    * Starting at 0xdf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e1f);
      assert s1.Peek(0) == 0xe1f;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x41b;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s2, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 207
    * Starting at 0xe1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x41b;
      assert s1.Peek(11) == 0x1fc;
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
      assert s11.Peek(6) == 0xd2e;
      assert s11.Peek(10) == 0x307;
      assert s11.Peek(12) == 0x41b;
      assert s11.Peek(13) == 0x1fc;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0e42);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s264(s20, gas - 1)
      else
        ExecuteFromCFGNode_s263(s20, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 208
    * Starting at 0xe3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x41b;
      assert s1.Peek(9) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x02f3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s6, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 209
    * Starting at 0xe42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x41b

    requires s0.stack[10] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x41b;
      assert s1.Peek(10) == 0x1fc;
      var s2 := Push2(s1, 0x0e4c);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0d84);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s6, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 188
    * Starting at 0xd84
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xe4c

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x41b

    requires s0.stack[13] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe4c;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x41b;
      assert s1.Peek(13) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s266(s4, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 189
    * Starting at 0xd89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x41b;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0dbf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s273(s7, gas - 1)
      else
        ExecuteFromCFGNode_s267(s7, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 190
    * Starting at 0xd92
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x41b;
      assert s1.Peek(17) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0da5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s270(s9, gas - 1)
      else
        ExecuteFromCFGNode_s268(s9, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 191
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da5);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x41b;
      assert s1.Peek(17) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s3, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xda5

    requires s0.stack[6] == 0xe4c

    requires s0.stack[10] == 0xd2e

    requires s0.stack[14] == 0x307

    requires s0.stack[16] == 0x41b

    requires s0.stack[17] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x41b;
      assert s1.Peek(17) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xda5;
      assert s11.Peek(8) == 0xe4c;
      assert s11.Peek(12) == 0xd2e;
      assert s11.Peek(16) == 0x307;
      assert s11.Peek(18) == 0x41b;
      assert s11.Peek(19) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 270
    * Segment Id for this node is: 192
    * Starting at 0xda5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x41b;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0db2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s272(s7, gas - 1)
      else
        ExecuteFromCFGNode_s271(s7, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 193
    * Starting at 0xdae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x41b;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s272(s4, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 194
    * Starting at 0xdb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x41b;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0d89);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s11, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 195
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x41b

    requires s0.stack[16] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x41b;
      assert s1.Peek(16) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s8, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 210
    * Starting at 0xe4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x41b

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x41b;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0e60);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s277(s10, gas - 1)
      else
        ExecuteFromCFGNode_s275(s10, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 211
    * Starting at 0xe59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x41b

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e60);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x41b;
      assert s1.Peek(13) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s3, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xe60

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x41b

    requires s0.stack[13] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x41b;
      assert s1.Peek(13) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe60;
      assert s11.Peek(8) == 0xd2e;
      assert s11.Peek(12) == 0x307;
      assert s11.Peek(14) == 0x41b;
      assert s11.Peek(15) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 277
    * Segment Id for this node is: 212
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x41b

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x41b;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s8, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 204
    * Starting at 0xe03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x41b;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e14);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s7, gas - 1)
      else
        ExecuteFromCFGNode_s279(s7, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 205
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e14);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x41b;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s3, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xe14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x41b

    requires s0.stack[12] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x41b;
      assert s1.Peek(12) == 0x1fc;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe14;
      assert s11.Peek(7) == 0xd2e;
      assert s11.Peek(11) == 0x307;
      assert s11.Peek(13) == 0x41b;
      assert s11.Peek(14) == 0x1fc;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 281
    * Segment Id for this node is: 206
    * Starting at 0xe14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x41b;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x02f3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s8, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 203
    * Starting at 0xdf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x41b

    requires s0.stack[11] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x41b;
      assert s1.Peek(11) == 0x1fc;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x02f3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s7, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 47
    * Starting at 0x1e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e7 as nat
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
      var s5 := Push2(s4, 0x01f3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s6, gas - 1)
      else
        ExecuteFromCFGNode_s284(s6, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 48
    * Starting at 0x1ef
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ef as nat
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

  /** Node 285
    * Segment Id for this node is: 49
    * Starting at 0x1f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x01fc);
      var s4 := Push2(s3, 0x036c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s5, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 81
    * Starting at 0x36c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x1fc;
      var s12 := Push2(s11, 0x039f);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s288(s13, gas - 1)
      else
        ExecuteFromCFGNode_s287(s13, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 82
    * Starting at 0x37f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1fc;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0396);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x396;
      assert s11.Peek(2) == 0x1fc;
      var s12 := Push2(s11, 0x0ea1);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s13, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 84
    * Starting at 0x39f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(4) == 0x1fc;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := And(s13);
      var s15 := Swap1(s14);
      var s16 := Push32(s15, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s17 := Swap1(s16);
      var s18 := Dup4(s17);
      var s19 := Swap1(s18);
      var s20 := Log3(s19);
      var s21 := Push1(s20, 0x00);
      assert s21.Peek(1) == 0x1fc;
      var s22 := Dup1(s21);
      var s23 := SLoad(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0xa0);
      var s27 := Shl(s26);
      var s28 := Sub(s27);
      var s29 := Not(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(2) == 0x1fc;
      var s32 := SStore(s31);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s33, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 12
    * Starting at 0x7f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
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
      var s5 := Push2(s4, 0x00d2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s498(s6, gas - 1)
      else
        ExecuteFromCFGNode_s290(s6, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 13
    * Starting at 0x8b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0122);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s479(s5, gas - 1)
      else
        ExecuteFromCFGNode_s291(s5, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 14
    * Starting at 0x96
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0152);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s438(s5, gas - 1)
      else
        ExecuteFromCFGNode_s292(s5, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 15
    * Starting at 0xa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0175);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s310(s5, gas - 1)
      else
        ExecuteFromCFGNode_s293(s5, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 16
    * Starting at 0xac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0195);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s5, gas - 1)
      else
        ExecuteFromCFGNode_s294(s5, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 17
    * Starting at 0xb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s296(s5, gas - 1)
      else
        ExecuteFromCFGNode_s295(s5, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 18
    * Starting at 0xc2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2 as nat
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

  /** Node 296
    * Segment Id for this node is: 43
    * Starting at 0x1b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
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
      var s5 := Push2(s4, 0x01bd);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s298(s6, gas - 1)
      else
        ExecuteFromCFGNode_s297(s6, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 44
    * Starting at 0x1b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b9 as nat
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

  /** Node 298
    * Segment Id for this node is: 45
    * Starting at 0x1bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0167);
      var s4 := Push2(s3, 0x01cc);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0d11);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s8, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 178
    * Starting at 0xd11
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1cc

    requires s0.stack[3] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1cc;
      assert s1.Peek(3) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d23);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s10, gas - 1)
      else
        ExecuteFromCFGNode_s300(s10, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 179
    * Starting at 0xd1f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1cc

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1cc;
      assert s1.Peek(5) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 301
    * Segment Id for this node is: 180
    * Starting at 0xd23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1cc

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1cc;
      assert s1.Peek(4) == 0x167;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0d2e);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s7, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x1cc

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2e;
      assert s1.Peek(6) == 0x1cc;
      assert s1.Peek(7) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xd2e;
      assert s11.Peek(8) == 0x1cc;
      assert s11.Peek(9) == 0x167;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s304(s12, gas - 1)
      else
        ExecuteFromCFGNode_s303(s12, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x1cc

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(7) == 0x1cc;
      assert s1.Peek(8) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 304
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd2e

    requires s0.stack[6] == 0x1cc

    requires s0.stack[7] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd2e;
      assert s1.Peek(6) == 0x1cc;
      assert s1.Peek(7) == 0x167;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s305(s3, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1cc

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1cc;
      assert s1.Peek(5) == 0x167;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s7, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 46
    * Starting at 0x1cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x167;
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
      assert s11.Peek(1) == 0x167;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Swap1(s15);
      var s17 := Keccak256(s16);
      var s18 := SLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s20, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 40
    * Starting at 0x195
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x195 as nat
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
      var s5 := Push2(s4, 0x01a1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s309(s6, gas - 1)
      else
        ExecuteFromCFGNode_s308(s6, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 41
    * Starting at 0x19d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19d as nat
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

  /** Node 309
    * Segment Id for this node is: 42
    * Starting at 0x1a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x09);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0119);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s11, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 36
    * Starting at 0x175
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
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
      var s5 := Push2(s4, 0x0181);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s312(s6, gas - 1)
      else
        ExecuteFromCFGNode_s311(s6, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 37
    * Starting at 0x17d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17d as nat
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

  /** Node 312
    * Segment Id for this node is: 38
    * Starting at 0x181
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x181 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0142);
      var s4 := Push2(s3, 0x0190);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0cd0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s8, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 173
    * Starting at 0xcd0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x190

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x190;
      assert s1.Peek(3) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0ce5);
      assert s11.Peek(0) == 0xce5;
      assert s11.Peek(7) == 0x190;
      assert s11.Peek(8) == 0x142;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s315(s12, gas - 1)
      else
        ExecuteFromCFGNode_s314(s12, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 174
    * Starting at 0xce1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x190

    requires s0.stack[6] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x190;
      assert s1.Peek(7) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 315
    * Segment Id for this node is: 175
    * Starting at 0xce5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x190

    requires s0.stack[6] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x190;
      assert s1.Peek(6) == 0x142;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0cf0);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s7, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xcf0

    requires s0.stack[8] == 0x190

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcf0;
      assert s1.Peek(8) == 0x190;
      assert s1.Peek(9) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xcf0;
      assert s11.Peek(10) == 0x190;
      assert s11.Peek(11) == 0x142;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s318(s12, gas - 1)
      else
        ExecuteFromCFGNode_s317(s12, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xcf0

    requires s0.stack[8] == 0x190

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xcf0;
      assert s1.Peek(9) == 0x190;
      assert s1.Peek(10) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 318
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xcf0

    requires s0.stack[8] == 0x190

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcf0;
      assert s1.Peek(8) == 0x190;
      assert s1.Peek(9) == 0x142;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s3, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 176
    * Starting at 0xcf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x190

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x190;
      assert s1.Peek(7) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0d00);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0c8c);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s11, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xd00

    requires s0.stack[8] == 0x190

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd00;
      assert s1.Peek(8) == 0x190;
      assert s1.Peek(9) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xd00;
      assert s11.Peek(10) == 0x190;
      assert s11.Peek(11) == 0x142;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s12, gas - 1)
      else
        ExecuteFromCFGNode_s321(s12, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xd00

    requires s0.stack[8] == 0x190

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xd00;
      assert s1.Peek(9) == 0x190;
      assert s1.Peek(10) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 322
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xd00

    requires s0.stack[8] == 0x190

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd00;
      assert s1.Peek(8) == 0x190;
      assert s1.Peek(9) == 0x142;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s3, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 177
    * Starting at 0xd00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x190

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x190;
      assert s1.Peek(7) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap6(s2);
      var s4 := Swap3(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(0) == 0x190;
      assert s11.Peek(5) == 0x142;
      var s12 := Swap2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s16, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 39
    * Starting at 0x190
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x190 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x142;
      var s2 := Push2(s1, 0x031a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s3, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 77
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0327);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0749);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s8, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 115
    * Starting at 0x749
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x749 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x0787);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s6, gas - 1)
      else
        ExecuteFromCFGNode_s327(s6, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 116
    * Starting at 0x752
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x752 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 11, 0x16995c9bc8185b5bdd5b9d);
      var s19 := Push1(s18, 0xaa);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x327;
      assert s21.Peek(11) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s28, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 83
    * Starting at 0x396
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
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

  /** Node 329
    * Segment Id for this node is: 117
    * Starting at 0x787
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x787 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x03);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Push2(s5, 0x07e4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s7, gas - 1)
      else
        ExecuteFromCFGNode_s330(s7, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 118
    * Starting at 0x792
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup5(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := And(s11);
      var s13 := Eq(s12);
      var s14 := Push2(s13, 0x07e4);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s15, gas - 1)
      else
        ExecuteFromCFGNode_s331(s15, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 119
    * Starting at 0x7a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x13);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 19, 0x151c98591a5b99c81b9bdd08195b98589b1959);
      var s19 := Push1(s18, 0x6a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x327;
      assert s21.Peek(11) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s28, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 120
    * Starting at 0x7e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push1(s19, 0xff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x327;
      assert s21.Peek(9) == 0x142;
      var s22 := Dup1(s21);
      var s23 := Push2(s22, 0x0823);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s24, gas - 1)
      else
        ExecuteFromCFGNode_s333(s24, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 121
    * Starting at 0x806
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x806 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push1(s19, 0xff);
      var s21 := And(s20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s334(s21, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 122
    * Starting at 0x823
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x823 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0838);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s4, gas - 1)
      else
        ExecuteFromCFGNode_s335(s4, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 123
    * Starting at 0x829
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x829 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0833);
      assert s1.Peek(0) == 0x833;
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0b9d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s6, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 159
    * Starting at 0xb9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x833

    requires s0.stack[7] == 0x327

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x833;
      assert s1.Peek(7) == 0x327;
      assert s1.Peek(12) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x833;
      assert s11.Peek(10) == 0x327;
      assert s11.Peek(15) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup1(s18);
      var s20 := SLoad(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x833;
      assert s21.Peek(11) == 0x327;
      assert s21.Peek(16) == 0x142;
      var s22 := Swap3(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0bc5);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0e8e);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s29, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 216
    * Starting at 0xe8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xbc5

    requires s0.stack[9] == 0x833

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbc5;
      assert s1.Peek(9) == 0x833;
      assert s1.Peek(13) == 0x327;
      assert s1.Peek(18) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s340(s10, gas - 1)
      else
        ExecuteFromCFGNode_s338(s10, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 217
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xbc5

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbc5;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s3, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0xbc5

    requires s0.stack[11] == 0x833

    requires s0.stack[15] == 0x327

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbc5;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0xbc5;
      assert s11.Peek(13) == 0x833;
      assert s11.Peek(17) == 0x327;
      assert s11.Peek(22) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 340
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xbc5

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbc5;
      assert s1.Peek(10) == 0x833;
      assert s1.Peek(14) == 0x327;
      assert s1.Peek(19) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s6, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 160
    * Starting at 0xbc5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x833

    requires s0.stack[11] == 0x327

    requires s0.stack[16] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x833;
      assert s1.Peek(11) == 0x327;
      assert s1.Peek(16) == 0x142;
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
      assert s11.Peek(4) == 0x833;
      assert s11.Peek(8) == 0x327;
      assert s11.Peek(13) == 0x142;
      var s12 := Dup3(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x20);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(5) == 0x833;
      assert s21.Peek(9) == 0x327;
      assert s21.Peek(14) == 0x142;
      var s22 := Dup2(s21);
      var s23 := Keccak256(s22);
      var s24 := Dup1(s23);
      var s25 := SLoad(s24);
      var s26 := Dup4(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x0bf2);
      var s30 := Swap1(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(2) == 0xbf2;
      assert s31.Peek(9) == 0x833;
      assert s31.Peek(13) == 0x327;
      assert s31.Peek(18) == 0x142;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0ef3);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s34, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 222
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xbf2

    requires s0.stack[9] == 0x833

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbf2;
      assert s1.Peek(9) == 0x833;
      assert s1.Peek(13) == 0x327;
      assert s1.Peek(18) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s345(s10, gas - 1)
      else
        ExecuteFromCFGNode_s343(s10, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 223
    * Starting at 0xeff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xbf2

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbf2;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s3, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0xbf2

    requires s0.stack[11] == 0x833

    requires s0.stack[15] == 0x327

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0xbf2;
      assert s1.Peek(11) == 0x833;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0xbf2;
      assert s11.Peek(13) == 0x833;
      assert s11.Peek(17) == 0x327;
      assert s11.Peek(22) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 345
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xbf2

    requires s0.stack[10] == 0x833

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbf2;
      assert s1.Peek(10) == 0x833;
      assert s1.Peek(14) == 0x327;
      assert s1.Peek(19) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s6, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 161
    * Starting at 0xbf2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x833

    requires s0.stack[11] == 0x327

    requires s0.stack[16] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x833;
      assert s1.Peek(11) == 0x327;
      assert s1.Peek(16) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x833;
      assert s11.Peek(10) == 0x327;
      assert s11.Peek(15) == 0x142;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := And(s14);
      var s16 := Dup4(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x833;
      assert s21.Peek(10) == 0x327;
      assert s21.Peek(15) == 0x142;
      var s22 := And(s21);
      var s23 := Push32(s22, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s24 := Dup4(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x073c);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x73c;
      assert s31.Peek(9) == 0x833;
      assert s31.Peek(13) == 0x327;
      assert s31.Peek(18) == 0x142;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s34, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 114
    * Starting at 0x73c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[7] == 0x833

    requires s0.stack[11] == 0x327

    requires s0.stack[16] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x833;
      assert s1.Peek(11) == 0x327;
      assert s1.Peek(16) == 0x142;
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
      assert s11.Peek(0) == 0x833;
      assert s11.Peek(4) == 0x327;
      assert s11.Peek(9) == 0x142;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s348(s12, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 124
    * Starting at 0x833
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x833 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s349(s5, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 78
    * Starting at 0x327
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x327 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x02);
      var s14 := Push1(s13, 0x20);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup4(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x142;
      var s22 := Caller(s21);
      var s23 := Dup1(s22);
      var s24 := Dup6(s23);
      var s25 := MStore(s24);
      var s26 := Swap3(s25);
      var s27 := MStore(s26);
      var s28 := Swap1(s27);
      var s29 := Swap2(s28);
      var s30 := Keccak256(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(6) == 0x142;
      var s32 := Push2(s31, 0x0362);
      var s33 := Swap2(s32);
      var s34 := Dup7(s33);
      var s35 := Swap2(s34);
      var s36 := Push2(s35, 0x035d);
      var s37 := Swap1(s36);
      var s38 := Dup7(s37);
      var s39 := Swap1(s38);
      var s40 := Push2(s39, 0x0e8e);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s41, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 216
    * Starting at 0xe8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x35d

    requires s0.stack[5] == 0x362

    requires s0.stack[10] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x35d;
      assert s1.Peek(5) == 0x362;
      assert s1.Peek(10) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s353(s10, gas - 1)
      else
        ExecuteFromCFGNode_s351(s10, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 217
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x35d

    requires s0.stack[6] == 0x362

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x35d;
      assert s1.Peek(7) == 0x362;
      assert s1.Peek(12) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s3, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x35d

    requires s0.stack[7] == 0x362

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x35d;
      assert s1.Peek(7) == 0x362;
      assert s1.Peek(12) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x35d;
      assert s11.Peek(9) == 0x362;
      assert s11.Peek(14) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 353
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x35d

    requires s0.stack[6] == 0x362

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35d;
      assert s1.Peek(6) == 0x362;
      assert s1.Peek(11) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s6, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 79
    * Starting at 0x35d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x362

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x362;
      assert s1.Peek(8) == 0x142;
      var s2 := Push2(s1, 0x0624);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s3, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 108
    * Starting at 0x624
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x624 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x362

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x362;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0686);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s358(s10, gas - 1)
      else
        ExecuteFromCFGNode_s356(s10, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 109
    * Starting at 0x633
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x633 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x362

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x362;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x362;
      assert s11.Peek(11) == 0x142;
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
      assert s21.Peek(6) == 0x362;
      assert s21.Peek(11) == 0x142;
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
      assert s31.Peek(4) == 0x362;
      assert s31.Peek(9) == 0x142;
      var s32 := Push2(s31, 0x0396);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s33, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 83
    * Starting at 0x396
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x362

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x362;
      assert s1.Peek(9) == 0x142;
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

  /** Node 358
    * Segment Id for this node is: 110
    * Starting at 0x686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x362

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x362;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06e7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s360(s10, gas - 1)
      else
        ExecuteFromCFGNode_s359(s10, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 111
    * Starting at 0x695
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x695 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x362

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x362;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x362;
      assert s11.Peek(11) == 0x142;
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
      assert s21.Peek(6) == 0x362;
      assert s21.Peek(11) == 0x142;
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
      assert s31.Peek(4) == 0x362;
      assert s31.Peek(9) == 0x142;
      var s32 := Push2(s31, 0x0396);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s33, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 112
    * Starting at 0x6e7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x362

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x362;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x362;
      assert s11.Peek(12) == 0x142;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x02);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x362;
      assert s21.Peek(15) == 0x142;
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
      assert s31.Peek(8) == 0x362;
      assert s31.Peek(13) == 0x142;
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
      ExecuteFromCFGNode_s361(s41, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 113
    * Starting at 0x717
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x717 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x362

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x362;
      assert s1.Peek(14) == 0x142;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s362(s5, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 114
    * Starting at 0x73c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x362

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x362;
      assert s1.Peek(12) == 0x142;
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
      assert s11.Peek(0) == 0x362;
      assert s11.Peek(5) == 0x142;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s12, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 80
    * Starting at 0x362
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x362 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x142;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s9, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 125
    * Starting at 0x838
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x838 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x085d);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s18, gas - 1)
      else
        ExecuteFromCFGNode_s365(s18, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 126
    * Starting at 0x850
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x850 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push2(s1, 0x0858);
      var s3 := Push2(s2, 0x02f9);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s4, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 74
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x858

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x858;
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0307);
      var s4 := Push1(s3, 0x09);
      var s5 := Push1(s4, 0x0a);
      var s6 := Push2(s5, 0x0e68);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s7, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 213
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x307

    requires s0.stack[4] == 0x858

    requires s0.stack[8] == 0x327

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x307;
      assert s1.Peek(4) == 0x858;
      assert s1.Peek(8) == 0x327;
      assert s1.Peek(13) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d2e);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0dc7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s9, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 196
    * Starting at 0xdc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xd2e

    requires s0.stack[6] == 0x307

    requires s0.stack[8] == 0x858

    requires s0.stack[12] == 0x327

    requires s0.stack[17] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x327;
      assert s1.Peek(17) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0dd6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s412(s5, gas - 1)
      else
        ExecuteFromCFGNode_s369(s5, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 197
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x327;
      assert s1.Peek(17) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s4, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x327;
      assert s1.Peek(18) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s6, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x307

    requires s0.stack[6] == 0x858

    requires s0.stack[10] == 0x327

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(6) == 0x858;
      assert s1.Peek(10) == 0x327;
      assert s1.Peek(15) == 0x142;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s7, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 75
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x858

    requires s0.stack[6] == 0x327

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x858;
      assert s1.Peek(6) == 0x327;
      assert s1.Peek(11) == 0x142;
      var s2 := Push2(s1, 0x0315);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x3b9aca00);
      var s5 := Push2(s4, 0x0e77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s6, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 214
    * Starting at 0xe77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x315

    requires s0.stack[4] == 0x858

    requires s0.stack[8] == 0x327

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x315;
      assert s1.Peek(4) == 0x858;
      assert s1.Peek(8) == 0x327;
      assert s1.Peek(13) == 0x142;
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
      assert s11.Peek(5) == 0x315;
      assert s11.Peek(7) == 0x858;
      assert s11.Peek(11) == 0x327;
      assert s11.Peek(16) == 0x142;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x02f3);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s376(s14, gas - 1)
      else
        ExecuteFromCFGNode_s374(s14, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 215
    * Starting at 0xe87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x858

    requires s0.stack[9] == 0x327

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x858;
      assert s1.Peek(10) == 0x327;
      assert s1.Peek(15) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s3, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x315

    requires s0.stack[6] == 0x858

    requires s0.stack[10] == 0x327

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x858;
      assert s1.Peek(10) == 0x327;
      assert s1.Peek(15) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x315;
      assert s11.Peek(8) == 0x858;
      assert s11.Peek(12) == 0x327;
      assert s11.Peek(17) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 376
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x858

    requires s0.stack[9] == 0x327

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x315;
      assert s1.Peek(5) == 0x858;
      assert s1.Peek(9) == 0x327;
      assert s1.Peek(14) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s6, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 76
    * Starting at 0x315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x858

    requires s0.stack[6] == 0x327

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x858;
      assert s1.Peek(6) == 0x327;
      assert s1.Peek(11) == 0x142;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s378(s5, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 127
    * Starting at 0x858
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x858 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Eq(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s379(s4, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 128
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0918);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s4, gas - 1)
      else
        ExecuteFromCFGNode_s380(s4, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 129
    * Starting at 0x863
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x863 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup4(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x327;
      assert s11.Peek(9) == 0x142;
      var s12 := Push1(s11, 0x0c);
      var s13 := Push1(s12, 0x20);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Swap1(s15);
      var s17 := Keccak256(s16);
      var s18 := SLoad(s17);
      var s19 := Push2(s18, 0x0886);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(2) == 0x886;
      assert s21.Peek(6) == 0x327;
      assert s21.Peek(11) == 0x142;
      var s22 := Push2(s21, 0x0ef3);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s23, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 222
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x886

    requires s0.stack[6] == 0x327

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x886;
      assert s1.Peek(6) == 0x327;
      assert s1.Peek(11) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s384(s10, gas - 1)
      else
        ExecuteFromCFGNode_s382(s10, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 223
    * Starting at 0xeff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x886

    requires s0.stack[7] == 0x327

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x886;
      assert s1.Peek(8) == 0x327;
      assert s1.Peek(13) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s3, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x886

    requires s0.stack[8] == 0x327

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x886;
      assert s1.Peek(8) == 0x327;
      assert s1.Peek(13) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x886;
      assert s11.Peek(10) == 0x327;
      assert s11.Peek(15) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 384
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x886

    requires s0.stack[7] == 0x327

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x886;
      assert s1.Peek(7) == 0x327;
      assert s1.Peek(12) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s6, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 130
    * Starting at 0x886
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x886 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Number(s1);
      var s3 := Lt(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08ac);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s387(s7, gas - 1)
      else
        ExecuteFromCFGNode_s386(s7, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 131
    * Starting at 0x88f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0d);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Dup2(s19);
      var s21 := Gt(s20);
      assert s21.Peek(4) == 0x327;
      assert s21.Peek(9) == 0x142;
      var s22 := IsZero(s21);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s387(s22, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 132
    * Starting at 0x8ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Push2(s1, 0x08ea);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s389(s3, gas - 1)
      else
        ExecuteFromCFGNode_s388(s3, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 133
    * Starting at 0x8b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151e08185b5bdd5b9d081b1a5b5a5d);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x327;
      assert s21.Peek(11) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s28, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 134
    * Starting at 0x8ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0d);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Dup2(s16);
      var s18 := Keccak256(s17);
      var s19 := Dup1(s18);
      var s20 := SLoad(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(7) == 0x327;
      assert s21.Peek(12) == 0x142;
      var s22 := Swap3(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0912);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0e8e);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s29, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 216
    * Starting at 0xe8e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x912

    requires s0.stack[9] == 0x327

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x912;
      assert s1.Peek(9) == 0x327;
      assert s1.Peek(14) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s393(s10, gas - 1)
      else
        ExecuteFromCFGNode_s391(s10, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 217
    * Starting at 0xe9a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x912

    requires s0.stack[10] == 0x327

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x912;
      assert s1.Peek(11) == 0x327;
      assert s1.Peek(16) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s3, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x912

    requires s0.stack[11] == 0x327

    requires s0.stack[16] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x912;
      assert s1.Peek(11) == 0x327;
      assert s1.Peek(16) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x912;
      assert s11.Peek(13) == 0x327;
      assert s11.Peek(18) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 393
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x912

    requires s0.stack[10] == 0x327

    requires s0.stack[15] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x912;
      assert s1.Peek(10) == 0x327;
      assert s1.Peek(15) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s6, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 135
    * Starting at 0x912
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x912 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x327

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x327;
      assert s1.Peek(12) == 0x142;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := SStore(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s395(s6, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 136
    * Starting at 0x918
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x918 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x07);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0943);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s397(s18, gas - 1)
      else
        ExecuteFromCFGNode_s396(s18, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 137
    * Starting at 0x930
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x930 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x0a);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := IsZero(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s397(s15, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 138
    * Starting at 0x943
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x943 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Push2(s2, 0x095b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s399(s4, gas - 1)
      else
        ExecuteFromCFGNode_s398(s4, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 139
    * Starting at 0x949
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x949 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x09);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s399(s14, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 140
    * Starting at 0x95b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x327

    requires s0.stack[9] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0a3e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s411(s4, gas - 1)
      else
        ExecuteFromCFGNode_s400(s4, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 141
    * Starting at 0x961
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x961 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x09a4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s402(s7, gas - 1)
      else
        ExecuteFromCFGNode_s401(s7, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 142
    * Starting at 0x96b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151e08185b5bdd5b9d081b1a5b5a5d);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x327;
      assert s21.Peek(11) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s28, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 143
    * Starting at 0x9a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x09c7);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x9c7;
      assert s11.Peek(8) == 0x327;
      assert s11.Peek(13) == 0x142;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x20);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0x9c7;
      assert s21.Peek(8) == 0x327;
      assert s21.Peek(13) == 0x142;
      var s22 := Keccak256(s21);
      var s23 := SLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s25, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 144
    * Starting at 0x9c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x327

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x327;
      assert s1.Peek(11) == 0x142;
      var s2 := Push2(s1, 0x09d1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0ef3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s6, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 222
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x9d1

    requires s0.stack[7] == 0x327

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9d1;
      assert s1.Peek(7) == 0x327;
      assert s1.Peek(12) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02f3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s407(s10, gas - 1)
      else
        ExecuteFromCFGNode_s405(s10, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 223
    * Starting at 0xeff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x9d1

    requires s0.stack[8] == 0x327

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x9d1;
      assert s1.Peek(9) == 0x327;
      assert s1.Peek(14) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s3, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x9d1

    requires s0.stack[9] == 0x327

    requires s0.stack[14] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x9d1;
      assert s1.Peek(9) == 0x327;
      assert s1.Peek(14) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x9d1;
      assert s11.Peek(11) == 0x327;
      assert s11.Peek(16) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 407
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x9d1

    requires s0.stack[8] == 0x327

    requires s0.stack[13] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9d1;
      assert s1.Peek(8) == 0x327;
      assert s1.Peek(13) == 0x142;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s6, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 145
    * Starting at 0x9d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x327

    requires s0.stack[10] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x327;
      assert s1.Peek(10) == 0x142;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0a15);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s410(s5, gas - 1)
      else
        ExecuteFromCFGNode_s409(s5, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 146
    * Starting at 0x9d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x327;
      assert s1.Peek(9) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x13);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 19, 0x15d85b1b195d08185b5bdd5b9d081b1a5b5a5d);
      var s19 := Push1(s18, 0x6a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x327;
      assert s21.Peek(11) == 0x142;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0396);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s28, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 147
    * Starting at 0xa15
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa15 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x327;
      assert s11.Peek(11) == 0x142;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0c);
      var s14 := Push1(s13, 0x20);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Dup1(s18);
      var s20 := Dup4(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(7) == 0x327;
      assert s21.Peek(12) == 0x142;
      var s22 := Number(s21);
      var s23 := Swap1(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x0d);
      var s26 := Swap1(s25);
      var s27 := Swap2(s26);
      var s28 := MStore(s27);
      var s29 := Swap1(s28);
      var s30 := Keccak256(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(5) == 0x327;
      assert s31.Peek(10) == 0x142;
      var s32 := Swap1(s31);
      var s33 := SStore(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s411(s33, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 148
    * Starting at 0xa3e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x327

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x327;
      assert s1.Peek(8) == 0x142;
      var s2 := Push2(s1, 0x0833);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b9d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s7, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 198
    * Starting at 0xdd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x327;
      assert s1.Peek(18) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0de3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s414(s4, gas - 1)
      else
        ExecuteFromCFGNode_s413(s4, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 199
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x327;
      assert s1.Peek(17) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s4, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 200
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x327;
      assert s1.Peek(18) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0df9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s437(s7, gas - 1)
      else
        ExecuteFromCFGNode_s415(s7, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 201
    * Starting at 0xded
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e03);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s433(s5, gas - 1)
      else
        ExecuteFromCFGNode_s416(s5, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 202
    * Starting at 0xdf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e1f);
      assert s1.Peek(0) == 0xe1f;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s2, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 207
    * Starting at 0xe1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x327;
      assert s1.Peek(19) == 0x142;
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
      assert s11.Peek(6) == 0xd2e;
      assert s11.Peek(10) == 0x307;
      assert s11.Peek(12) == 0x858;
      assert s11.Peek(16) == 0x327;
      assert s11.Peek(21) == 0x142;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0e42);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s419(s20, gas - 1)
      else
        ExecuteFromCFGNode_s418(s20, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 208
    * Starting at 0xe3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x858;
      assert s1.Peek(12) == 0x327;
      assert s1.Peek(17) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x02f3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s6, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 209
    * Starting at 0xe42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x858

    requires s0.stack[13] == 0x327

    requires s0.stack[18] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x858;
      assert s1.Peek(13) == 0x327;
      assert s1.Peek(18) == 0x142;
      var s2 := Push2(s1, 0x0e4c);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0d84);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s6, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 188
    * Starting at 0xd84
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xe4c

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x858

    requires s0.stack[16] == 0x327

    requires s0.stack[21] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe4c;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x858;
      assert s1.Peek(16) == 0x327;
      assert s1.Peek(21) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s421(s4, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 189
    * Starting at 0xd89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x327;
      assert s1.Peek(24) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0dbf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s428(s7, gas - 1)
      else
        ExecuteFromCFGNode_s422(s7, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 190
    * Starting at 0xd92
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x858;
      assert s1.Peek(20) == 0x327;
      assert s1.Peek(25) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0da5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s425(s9, gas - 1)
      else
        ExecuteFromCFGNode_s423(s9, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 191
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da5);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x858;
      assert s1.Peek(20) == 0x327;
      assert s1.Peek(25) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s3, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[0] == 0xda5

    requires s0.stack[6] == 0xe4c

    requires s0.stack[10] == 0xd2e

    requires s0.stack[14] == 0x307

    requires s0.stack[16] == 0x858

    requires s0.stack[20] == 0x327

    requires s0.stack[25] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x858;
      assert s1.Peek(20) == 0x327;
      assert s1.Peek(25) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xda5;
      assert s11.Peek(8) == 0xe4c;
      assert s11.Peek(12) == 0xd2e;
      assert s11.Peek(16) == 0x307;
      assert s11.Peek(18) == 0x858;
      assert s11.Peek(22) == 0x327;
      assert s11.Peek(27) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 425
    * Segment Id for this node is: 192
    * Starting at 0xda5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x327;
      assert s1.Peek(24) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0db2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s427(s7, gas - 1)
      else
        ExecuteFromCFGNode_s426(s7, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 193
    * Starting at 0xdae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x327;
      assert s1.Peek(24) == 0x142;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s427(s4, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 194
    * Starting at 0xdb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x327;
      assert s1.Peek(24) == 0x142;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0d89);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s11, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 195
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x858

    requires s0.stack[19] == 0x327

    requires s0.stack[24] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x858;
      assert s1.Peek(19) == 0x327;
      assert s1.Peek(24) == 0x142;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s8, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 210
    * Starting at 0xe4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x327

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0e60);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s432(s10, gas - 1)
      else
        ExecuteFromCFGNode_s430(s10, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 211
    * Starting at 0xe59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x327

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e60);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x858;
      assert s1.Peek(16) == 0x327;
      assert s1.Peek(21) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s3, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xe60

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x858

    requires s0.stack[16] == 0x327

    requires s0.stack[21] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x858;
      assert s1.Peek(16) == 0x327;
      assert s1.Peek(21) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe60;
      assert s11.Peek(8) == 0xd2e;
      assert s11.Peek(12) == 0x307;
      assert s11.Peek(14) == 0x858;
      assert s11.Peek(18) == 0x327;
      assert s11.Peek(23) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 432
    * Segment Id for this node is: 212
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x327

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s8, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 204
    * Starting at 0xe03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x327;
      assert s1.Peek(19) == 0x142;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e14);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s436(s7, gas - 1)
      else
        ExecuteFromCFGNode_s434(s7, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 205
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e14);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s3, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xe14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x858

    requires s0.stack[15] == 0x327

    requires s0.stack[20] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x858;
      assert s1.Peek(15) == 0x327;
      assert s1.Peek(20) == 0x142;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe14;
      assert s11.Peek(7) == 0xd2e;
      assert s11.Peek(11) == 0x307;
      assert s11.Peek(13) == 0x858;
      assert s11.Peek(17) == 0x327;
      assert s11.Peek(22) == 0x142;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 436
    * Segment Id for this node is: 206
    * Starting at 0xe14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x327;
      assert s1.Peek(19) == 0x142;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x02f3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s8, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 203
    * Starting at 0xdf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x858

    requires s0.stack[14] == 0x327

    requires s0.stack[19] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x858;
      assert s1.Peek(14) == 0x327;
      assert s1.Peek(19) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x02f3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s7, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 32
    * Starting at 0x152
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
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
      var s5 := Push2(s4, 0x015e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s440(s6, gas - 1)
      else
        ExecuteFromCFGNode_s439(s6, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 33
    * Starting at 0x15a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a as nat
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

  /** Node 440
    * Segment Id for this node is: 34
    * Starting at 0x15e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0167);
      var s4 := Push2(s3, 0x02f9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s441(s5, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 74
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0307);
      var s4 := Push1(s3, 0x09);
      var s5 := Push1(s4, 0x0a);
      var s6 := Push2(s5, 0x0e68);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s7, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 213
    * Starting at 0xe68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x307

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x307;
      assert s1.Peek(4) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0d2e);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x0dc7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s9, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 196
    * Starting at 0xdc7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd2e

    requires s0.stack[6] == 0x307

    requires s0.stack[8] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0dd6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s453(s5, gas - 1)
      else
        ExecuteFromCFGNode_s444(s5, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 197
    * Starting at 0xdcf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s4, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s6, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 181
    * Starting at 0xd2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x307

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(6) == 0x167;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s7, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 75
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x167;
      var s2 := Push2(s1, 0x0315);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x3b9aca00);
      var s5 := Push2(s4, 0x0e77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s6, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 214
    * Starting at 0xe77
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x315

    requires s0.stack[4] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x315;
      assert s1.Peek(4) == 0x167;
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
      assert s11.Peek(5) == 0x315;
      assert s11.Peek(7) == 0x167;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x02f3);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s451(s14, gas - 1)
      else
        ExecuteFromCFGNode_s449(s14, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 215
    * Starting at 0xe87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02f3);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x167;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s3, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x2f3

    requires s0.stack[4] == 0x315

    requires s0.stack[6] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2f3;
      assert s1.Peek(4) == 0x315;
      assert s1.Peek(6) == 0x167;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x2f3;
      assert s11.Peek(6) == 0x315;
      assert s11.Peek(8) == 0x167;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 451
    * Segment Id for this node is: 73
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x315

    requires s0.stack[5] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x315;
      assert s1.Peek(5) == 0x167;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s6, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 76
    * Starting at 0x315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x167;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s5, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 198
    * Starting at 0xdd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0de3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s455(s4, gas - 1)
      else
        ExecuteFromCFGNode_s454(s4, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 199
    * Starting at 0xddc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xddc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s4, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 200
    * Starting at 0xde3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0df9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s478(s7, gas - 1)
      else
        ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 201
    * Starting at 0xded
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xded as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0e03);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s474(s5, gas - 1)
      else
        ExecuteFromCFGNode_s457(s5, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 202
    * Starting at 0xdf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e1f);
      assert s1.Peek(0) == 0xe1f;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x167;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s2, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 207
    * Starting at 0xe1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x167;
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
      assert s11.Peek(6) == 0xd2e;
      assert s11.Peek(10) == 0x307;
      assert s11.Peek(12) == 0x167;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0e42);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s460(s20, gas - 1)
      else
        ExecuteFromCFGNode_s459(s20, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 208
    * Starting at 0xe3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xd2e;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(8) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x02f3);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s6, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 209
    * Starting at 0xe42
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd2e

    requires s0.stack[7] == 0x307

    requires s0.stack[9] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd2e;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(9) == 0x167;
      var s2 := Push2(s1, 0x0e4c);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0d84);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s6, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 188
    * Starting at 0xd84
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xe4c

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe4c;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s462(s4, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 189
    * Starting at 0xd89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0dbf);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s469(s7, gas - 1)
      else
        ExecuteFromCFGNode_s463(s7, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 190
    * Starting at 0xd92
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x167;
      var s2 := Push1(s1, 0x00);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0da5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s9, gas - 1)
      else
        ExecuteFromCFGNode_s464(s9, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 191
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0da5);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x167;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s3, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xda5

    requires s0.stack[6] == 0xe4c

    requires s0.stack[10] == 0xd2e

    requires s0.stack[14] == 0x307

    requires s0.stack[16] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xda5;
      assert s1.Peek(6) == 0xe4c;
      assert s1.Peek(10) == 0xd2e;
      assert s1.Peek(14) == 0x307;
      assert s1.Peek(16) == 0x167;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xda5;
      assert s11.Peek(8) == 0xe4c;
      assert s11.Peek(12) == 0xd2e;
      assert s11.Peek(16) == 0x307;
      assert s11.Peek(18) == 0x167;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 466
    * Segment Id for this node is: 192
    * Starting at 0xda5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0db2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s468(s7, gas - 1)
      else
        ExecuteFromCFGNode_s467(s7, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 193
    * Starting at 0xdae
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x167;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s468(s4, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 194
    * Starting at 0xdb2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x167;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0d89);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s11, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 195
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0xe4c

    requires s0.stack[9] == 0xd2e

    requires s0.stack[13] == 0x307

    requires s0.stack[15] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe4c;
      assert s1.Peek(9) == 0xd2e;
      assert s1.Peek(13) == 0x307;
      assert s1.Peek(15) == 0x167;
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
    * Segment Id for this node is: 210
    * Starting at 0xe4c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x167;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0e60);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s473(s10, gas - 1)
      else
        ExecuteFromCFGNode_s471(s10, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 211
    * Starting at 0xe59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e60);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x167;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s3, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xe60

    requires s0.stack[6] == 0xd2e

    requires s0.stack[10] == 0x307

    requires s0.stack[12] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe60;
      assert s1.Peek(6) == 0xd2e;
      assert s1.Peek(10) == 0x307;
      assert s1.Peek(12) == 0x167;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe60;
      assert s11.Peek(8) == 0xd2e;
      assert s11.Peek(12) == 0x307;
      assert s11.Peek(14) == 0x167;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 473
    * Segment Id for this node is: 212
    * Starting at 0xe60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x167;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s8, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 204
    * Starting at 0xe03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x167;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e14);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s477(s7, gas - 1)
      else
        ExecuteFromCFGNode_s475(s7, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 205
    * Starting at 0xe0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e14);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x167;
      var s2 := Push2(s1, 0x0d6e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s3, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 187
    * Starting at 0xd6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xe14

    requires s0.stack[5] == 0xd2e

    requires s0.stack[9] == 0x307

    requires s0.stack[11] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe14;
      assert s1.Peek(5) == 0xd2e;
      assert s1.Peek(9) == 0x307;
      assert s1.Peek(11) == 0x167;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0xe14;
      assert s11.Peek(7) == 0xd2e;
      assert s11.Peek(11) == 0x307;
      assert s11.Peek(13) == 0x167;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 477
    * Segment Id for this node is: 206
    * Starting at 0xe14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x167;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x02f3);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s8, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 203
    * Starting at 0xdf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd2e

    requires s0.stack[8] == 0x307

    requires s0.stack[10] == 0x167

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd2e;
      assert s1.Peek(8) == 0x307;
      assert s1.Peek(10) == 0x167;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x02f3);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s7, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 27
    * Starting at 0x122
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122 as nat
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
      var s5 := Push2(s4, 0x012e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s481(s6, gas - 1)
      else
        ExecuteFromCFGNode_s480(s6, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 28
    * Starting at 0x12a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a as nat
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

  /** Node 481
    * Segment Id for this node is: 29
    * Starting at 0x12e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0142);
      var s4 := Push2(s3, 0x013d);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ca4);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s8, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 169
    * Starting at 0xca4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x13d

    requires s0.stack[3] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13d;
      assert s1.Peek(3) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cb7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s484(s11, gas - 1)
      else
        ExecuteFromCFGNode_s483(s11, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 170
    * Starting at 0xcb3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x13d

    requires s0.stack[5] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x13d;
      assert s1.Peek(6) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 484
    * Segment Id for this node is: 171
    * Starting at 0xcb7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x13d

    requires s0.stack[5] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x13d;
      assert s1.Peek(5) == 0x142;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0cc2);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0c8c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s7, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 166
    * Starting at 0xc8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcc2

    requires s0.stack[7] == 0x13d

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcc2;
      assert s1.Peek(7) == 0x13d;
      assert s1.Peek(8) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0ca1);
      assert s11.Peek(0) == 0xca1;
      assert s11.Peek(3) == 0xcc2;
      assert s11.Peek(9) == 0x13d;
      assert s11.Peek(10) == 0x142;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s487(s12, gas - 1)
      else
        ExecuteFromCFGNode_s486(s12, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 167
    * Starting at 0xc9d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcc2

    requires s0.stack[7] == 0x13d

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0xcc2;
      assert s1.Peek(8) == 0x13d;
      assert s1.Peek(9) == 0x142;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 487
    * Segment Id for this node is: 168
    * Starting at 0xca1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcc2

    requires s0.stack[7] == 0x13d

    requires s0.stack[8] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcc2;
      assert s1.Peek(7) == 0x13d;
      assert s1.Peek(8) == 0x142;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s3, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 172
    * Starting at 0xcc2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x13d

    requires s0.stack[6] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13d;
      assert s1.Peek(6) == 0x142;
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
      assert s11.Peek(1) == 0x13d;
      assert s11.Peek(4) == 0x142;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s13, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 30
    * Starting at 0x13d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x142;
      var s2 := Push2(s1, 0x02e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s3, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 71
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x142;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02ef);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0624);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s8, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 108
    * Starting at 0x624
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x624 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0686);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s493(s10, gas - 1)
      else
        ExecuteFromCFGNode_s492(s10, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 109
    * Starting at 0x633
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x633 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
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
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
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
      assert s31.Peek(4) == 0x2ef;
      assert s31.Peek(8) == 0x142;
      var s32 := Push2(s31, 0x0396);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s33, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 110
    * Starting at 0x686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06e7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s495(s10, gas - 1)
      else
        ExecuteFromCFGNode_s494(s10, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 111
    * Starting at 0x695
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x695 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2ef;
      assert s1.Peek(8) == 0x142;
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
      assert s11.Peek(6) == 0x2ef;
      assert s11.Peek(10) == 0x142;
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
      assert s21.Peek(6) == 0x2ef;
      assert s21.Peek(10) == 0x142;
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
      assert s31.Peek(4) == 0x2ef;
      assert s31.Peek(8) == 0x142;
      var s32 := Push2(s31, 0x0396);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s33, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 112
    * Starting at 0x6e7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2ef

    requires s0.stack[7] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ef;
      assert s1.Peek(7) == 0x142;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x2ef;
      assert s11.Peek(11) == 0x142;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x02);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x2ef;
      assert s21.Peek(14) == 0x142;
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
      assert s31.Peek(8) == 0x2ef;
      assert s31.Peek(12) == 0x142;
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
      ExecuteFromCFGNode_s496(s41, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 113
    * Starting at 0x717
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x717 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x2ef

    requires s0.stack[12] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x2ef;
      assert s1.Peek(13) == 0x142;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s497(s5, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 114
    * Starting at 0x73c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x2ef

    requires s0.stack[11] == 0x142

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2ef;
      assert s1.Peek(11) == 0x142;
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
      assert s11.Peek(0) == 0x2ef;
      assert s11.Peek(4) == 0x142;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s12, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 22
    * Starting at 0xd2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2 as nat
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
      var s5 := Push2(s4, 0x00de);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s500(s6, gas - 1)
      else
        ExecuteFromCFGNode_s499(s6, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 23
    * Starting at 0xda
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda as nat
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

  /** Node 500
    * Segment Id for this node is: 24
    * Starting at 0xde
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x15);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 21, 0x189bdb59481a5b8818481b595b595cc81ddbdc9b19);
      var s16 := Push1(s15, 0x5a);
      var s17 := Shl(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s21, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 19
    * Starting at 0xc6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x00cd);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s503(s4, gas - 1)
      else
        ExecuteFromCFGNode_s502(s4, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 20
    * Starting at 0xcc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0);
      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 503
    * Segment Id for this node is: 21
    * Starting at 0xcd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd as nat
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
