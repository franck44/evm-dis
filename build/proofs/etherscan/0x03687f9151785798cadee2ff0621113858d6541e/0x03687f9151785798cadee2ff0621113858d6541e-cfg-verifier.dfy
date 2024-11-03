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
      var s6 := Push2(s5, 0x00a7);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s606(s7, gas - 1)
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
      var s6 := Push4(s5, 0x39509351);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x006f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s345(s9, gas - 1)
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
      var s2 := Push4(s1, 0x39509351);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0165);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s5, gas - 1)
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
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0195);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s5, gas - 1)
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
      var s2 := Push4(s1, 0x7ef2ed0b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01c5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s5, gas - 1)
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
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01f5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0213);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x60
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0243);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00a7);
      assert s1.Peek(0) == 0xa7;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s2, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 16
    * Starting at 0xa7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
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

  /** Node 12
    * Segment Id for this node is: 53
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x025d);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0258);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x258;
      assert s11.Peek(3) == 0x25d;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0df0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s14, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 197
    * Starting at 0xdf0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x258

    requires s0.stack[3] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x258;
      assert s1.Peek(3) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0e06);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s11, gas - 1)
      else
        ExecuteFromCFGNode_s14(s11, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 198
    * Starting at 0xdfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x258

    requires s0.stack[5] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e05);
      assert s1.Peek(0) == 0xe05;
      assert s1.Peek(5) == 0x258;
      assert s1.Peek(6) == 0x25d;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s3, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xe05

    requires s0.stack[5] == 0x258

    requires s0.stack[6] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe05;
      assert s1.Peek(5) == 0x258;
      assert s1.Peek(6) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 16
    * Segment Id for this node is: 200
    * Starting at 0xe06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x258

    requires s0.stack[5] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x258;
      assert s1.Peek(5) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e13);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s9, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe13

    requires s0.stack[8] == 0x258

    requires s0.stack[9] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe13;
      assert s1.Peek(8) == 0x258;
      assert s1.Peek(9) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s10, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xe13

    requires s0.stack[11] == 0x258

    requires s0.stack[12] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xe13;
      assert s1.Peek(11) == 0x258;
      assert s1.Peek(12) == 0x25d;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s5, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xe13

    requires s0.stack[13] == 0x258

    requires s0.stack[14] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xe13;
      assert s1.Peek(13) == 0x258;
      assert s1.Peek(14) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s6, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xe13

    requires s0.stack[16] == 0x258

    requires s0.stack[17] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xe13;
      assert s1.Peek(16) == 0x258;
      assert s1.Peek(17) == 0x25d;
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
      ExecuteFromCFGNode_s21(s11, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xe13

    requires s0.stack[15] == 0x258

    requires s0.stack[16] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xe13;
      assert s1.Peek(15) == 0x258;
      assert s1.Peek(16) == 0x25d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s7, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xe13

    requires s0.stack[12] == 0x258

    requires s0.stack[13] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xe13;
      assert s1.Peek(12) == 0x258;
      assert s1.Peek(13) == 0x25d;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s5, gas - 1)
      else
        ExecuteFromCFGNode_s23(s5, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xe13

    requires s0.stack[11] == 0x258

    requires s0.stack[12] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xe13;
      assert s1.Peek(12) == 0x258;
      assert s1.Peek(13) == 0x25d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xe13

    requires s0.stack[11] == 0x258

    requires s0.stack[12] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xe13;
      assert s1.Peek(11) == 0x258;
      assert s1.Peek(12) == 0x25d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s3, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe13

    requires s0.stack[9] == 0x258

    requires s0.stack[10] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe13;
      assert s1.Peek(9) == 0x258;
      assert s1.Peek(10) == 0x25d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 201
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x258

    requires s0.stack[7] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x258;
      assert s1.Peek(7) == 0x25d;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0e24);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c61);
      assert s11.Peek(0) == 0xc61;
      assert s11.Peek(3) == 0xe24;
      assert s11.Peek(9) == 0x258;
      assert s11.Peek(10) == 0x25d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s12, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xe24

    requires s0.stack[8] == 0x258

    requires s0.stack[9] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe24;
      assert s1.Peek(8) == 0x258;
      assert s1.Peek(9) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s10, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xe24

    requires s0.stack[11] == 0x258

    requires s0.stack[12] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xe24;
      assert s1.Peek(11) == 0x258;
      assert s1.Peek(12) == 0x25d;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s5, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xe24

    requires s0.stack[13] == 0x258

    requires s0.stack[14] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xe24;
      assert s1.Peek(13) == 0x258;
      assert s1.Peek(14) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xe24

    requires s0.stack[16] == 0x258

    requires s0.stack[17] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xe24;
      assert s1.Peek(16) == 0x258;
      assert s1.Peek(17) == 0x25d;
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
      ExecuteFromCFGNode_s31(s11, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xe24

    requires s0.stack[15] == 0x258

    requires s0.stack[16] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xe24;
      assert s1.Peek(15) == 0x258;
      assert s1.Peek(16) == 0x25d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s7, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xe24

    requires s0.stack[12] == 0x258

    requires s0.stack[13] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xe24;
      assert s1.Peek(12) == 0x258;
      assert s1.Peek(13) == 0x25d;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s5, gas - 1)
      else
        ExecuteFromCFGNode_s33(s5, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xe24

    requires s0.stack[11] == 0x258

    requires s0.stack[12] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xe24;
      assert s1.Peek(12) == 0x258;
      assert s1.Peek(13) == 0x25d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 34
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xe24

    requires s0.stack[11] == 0x258

    requires s0.stack[12] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xe24;
      assert s1.Peek(11) == 0x258;
      assert s1.Peek(12) == 0x25d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s3, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xe24

    requires s0.stack[9] == 0x258

    requires s0.stack[10] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe24;
      assert s1.Peek(9) == 0x258;
      assert s1.Peek(10) == 0x25d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s6, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 202
    * Starting at 0xe24
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x258

    requires s0.stack[7] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x258;
      assert s1.Peek(7) == 0x25d;
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
      ExecuteFromCFGNode_s37(s10, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 54
    * Starting at 0x258
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x258 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x25d;
      var s2 := Push2(s1, 0x06a2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s3, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 105
    * Starting at 0x6a2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x25d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup5(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x25d;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(5) == 0x25d;
      var s22 := Dup4(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x25d;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Pop(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s39(s41, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 106
    * Starting at 0x720
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x720 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x25d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(2) == 0x25d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s4, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 55
    * Starting at 0x25d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x026a);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d28);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s8, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x26a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x26a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x26a;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s14, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x26a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x26a;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s5, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x26a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x26a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s9, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x26a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x26a;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s6, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x26a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x26a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s6, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 56
    * Starting at 0x26a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26a as nat
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

  /** Node 47
    * Segment Id for this node is: 49
    * Starting at 0x213
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x022d);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0228);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x228;
      assert s11.Peek(3) == 0x22d;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ca8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s14, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 165
    * Starting at 0xca8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x228

    requires s0.stack[3] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x228;
      assert s1.Peek(3) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cbe);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s11, gas - 1)
      else
        ExecuteFromCFGNode_s49(s11, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 166
    * Starting at 0xcb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x228

    requires s0.stack[5] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0cbd);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0x228;
      assert s1.Peek(6) == 0x22d;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s3, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xcbd

    requires s0.stack[5] == 0x228

    requires s0.stack[6] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0x228;
      assert s1.Peek(6) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 51
    * Segment Id for this node is: 168
    * Starting at 0xcbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x228

    requires s0.stack[5] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x228;
      assert s1.Peek(5) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ccb);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s9, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xccb

    requires s0.stack[8] == 0x228

    requires s0.stack[9] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xccb;
      assert s1.Peek(8) == 0x228;
      assert s1.Peek(9) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s10, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x228

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0x228;
      assert s1.Peek(12) == 0x22d;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s5, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xccb

    requires s0.stack[13] == 0x228

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xccb;
      assert s1.Peek(13) == 0x228;
      assert s1.Peek(14) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xccb

    requires s0.stack[16] == 0x228

    requires s0.stack[17] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xccb;
      assert s1.Peek(16) == 0x228;
      assert s1.Peek(17) == 0x22d;
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
      ExecuteFromCFGNode_s56(s11, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xccb

    requires s0.stack[15] == 0x228

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xccb;
      assert s1.Peek(15) == 0x228;
      assert s1.Peek(16) == 0x22d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s7, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xccb

    requires s0.stack[12] == 0x228

    requires s0.stack[13] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0x228;
      assert s1.Peek(13) == 0x22d;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s5, gas - 1)
      else
        ExecuteFromCFGNode_s58(s5, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x228

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0x228;
      assert s1.Peek(13) == 0x22d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 59
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x228

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0x228;
      assert s1.Peek(12) == 0x22d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s3, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xccb

    requires s0.stack[9] == 0x228

    requires s0.stack[10] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xccb;
      assert s1.Peek(9) == 0x228;
      assert s1.Peek(10) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s6, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 169
    * Starting at 0xccb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x228

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x228;
      assert s1.Peek(7) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0cdc);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c94);
      assert s11.Peek(0) == 0xc94;
      assert s11.Peek(3) == 0xcdc;
      assert s11.Peek(9) == 0x228;
      assert s11.Peek(10) == 0x22d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s12, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 163
    * Starting at 0xc94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xcdc

    requires s0.stack[8] == 0x228

    requires s0.stack[9] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcdc;
      assert s1.Peek(8) == 0x228;
      assert s1.Peek(9) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ca2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c7e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s10, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 159
    * Starting at 0xc7e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x228

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0x228;
      assert s1.Peek(12) == 0x22d;
      var s2 := Push2(s1, 0x0c87);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s5, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc87

    requires s0.stack[3] == 0xca2

    requires s0.stack[7] == 0xcdc

    requires s0.stack[13] == 0x228

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc87;
      assert s1.Peek(3) == 0xca2;
      assert s1.Peek(7) == 0xcdc;
      assert s1.Peek(13) == 0x228;
      assert s1.Peek(14) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s9, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 160
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xca2

    requires s0.stack[6] == 0xcdc

    requires s0.stack[12] == 0x228

    requires s0.stack[13] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0x228;
      assert s1.Peek(13) == 0x22d;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c91);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s5, gas - 1)
      else
        ExecuteFromCFGNode_s66(s5, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 161
    * Starting at 0xc8e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x228

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0x228;
      assert s1.Peek(13) == 0x22d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 67
    * Segment Id for this node is: 162
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x228

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0x228;
      assert s1.Peek(12) == 0x22d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s3, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 164
    * Starting at 0xca2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xcdc

    requires s0.stack[9] == 0x228

    requires s0.stack[10] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcdc;
      assert s1.Peek(9) == 0x228;
      assert s1.Peek(10) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s6, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 170
    * Starting at 0xcdc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x228

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x228;
      assert s1.Peek(7) == 0x22d;
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
      ExecuteFromCFGNode_s70(s10, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 50
    * Starting at 0x228
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x228 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x22d;
      var s2 := Push2(s1, 0x0685);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s3, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 102
    * Starting at 0x685
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x685 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0698);
      var s4 := Push2(s3, 0x0691);
      var s5 := Push2(s4, 0x0724);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s6, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x691

    requires s0.stack[1] == 0x698

    requires s0.stack[5] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x691;
      assert s1.Peek(1) == 0x698;
      assert s1.Peek(5) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s7, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 103
    * Starting at 0x691
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x691 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x698

    requires s0.stack[5] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x698;
      assert s1.Peek(5) == 0x22d;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x08ee);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s5, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 117
    * Starting at 0x8ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x698

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x698;
      assert s1.Peek(7) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x095c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s10, gas - 1)
      else
        ExecuteFromCFGNode_s75(s10, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 118
    * Starting at 0x922
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x922 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x698

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x698;
      assert s1.Peek(8) == 0x22d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0953);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1193);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s11, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 245
    * Starting at 0x1193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x953

    requires s0.stack[5] == 0x698

    requires s0.stack[9] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x953;
      assert s1.Peek(5) == 0x698;
      assert s1.Peek(9) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x953;
      assert s11.Peek(8) == 0x698;
      assert s11.Peek(12) == 0x22d;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11aa);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1171);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s18, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 242
    * Starting at 0x1171
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x11aa

    requires s0.stack[4] == 0x953

    requires s0.stack[8] == 0x698

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11aa;
      assert s1.Peek(4) == 0x953;
      assert s1.Peek(8) == 0x698;
      assert s1.Peek(12) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x117d);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s7, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x117d

    requires s0.stack[5] == 0x11aa

    requires s0.stack[8] == 0x953

    requires s0.stack[12] == 0x698

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x117d;
      assert s1.Peek(5) == 0x11aa;
      assert s1.Peek(8) == 0x953;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x117d;
      assert s11.Peek(6) == 0x11aa;
      assert s11.Peek(9) == 0x953;
      assert s11.Peek(13) == 0x698;
      assert s11.Peek(17) == 0x22d;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s15, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 243
    * Starting at 0x117d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x11aa

    requires s0.stack[6] == 0x953

    requires s0.stack[10] == 0x698

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11aa;
      assert s1.Peek(6) == 0x953;
      assert s1.Peek(10) == 0x698;
      assert s1.Peek(14) == 0x22d;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1188);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1123);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s7, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 241
    * Starting at 0x1123
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1123 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1188

    requires s0.stack[4] == 0x11aa

    requires s0.stack[7] == 0x953

    requires s0.stack[11] == 0x698

    requires s0.stack[15] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1188;
      assert s1.Peek(4) == 0x11aa;
      assert s1.Peek(7) == 0x953;
      assert s1.Peek(11) == 0x698;
      assert s1.Peek(15) == 0x22d;
      var s2 := Push32(s1, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1188;
      assert s11.Peek(4) == 0x11aa;
      assert s11.Peek(7) == 0x953;
      assert s11.Peek(11) == 0x698;
      assert s11.Peek(15) == 0x22d;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s13, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 244
    * Starting at 0x1188
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x11aa

    requires s0.stack[5] == 0x953

    requires s0.stack[9] == 0x698

    requires s0.stack[13] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11aa;
      assert s1.Peek(5) == 0x953;
      assert s1.Peek(9) == 0x698;
      assert s1.Peek(13) == 0x22d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s10, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 246
    * Starting at 0x11aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x953

    requires s0.stack[7] == 0x698

    requires s0.stack[11] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x953;
      assert s1.Peek(7) == 0x698;
      assert s1.Peek(11) == 0x22d;
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
    * Segment Id for this node is: 119
    * Starting at 0x953
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x953 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x698

    requires s0.stack[8] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x698;
      assert s1.Peek(8) == 0x22d;
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

  /** Node 84
    * Segment Id for this node is: 120
    * Starting at 0x95c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x698

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x698;
      assert s1.Peek(7) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x09ca);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s10, gas - 1)
      else
        ExecuteFromCFGNode_s85(s10, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 121
    * Starting at 0x990
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x990 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x698

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x698;
      assert s1.Peek(8) == 0x22d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09c1);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1221);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s11, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 251
    * Starting at 0x1221
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1221 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x9c1

    requires s0.stack[5] == 0x698

    requires s0.stack[9] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9c1;
      assert s1.Peek(5) == 0x698;
      assert s1.Peek(9) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x9c1;
      assert s11.Peek(8) == 0x698;
      assert s11.Peek(12) == 0x22d;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1238);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x11ff);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s18, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 248
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1238

    requires s0.stack[4] == 0x9c1

    requires s0.stack[8] == 0x698

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1238;
      assert s1.Peek(4) == 0x9c1;
      assert s1.Peek(8) == 0x698;
      assert s1.Peek(12) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x120b);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s7, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x120b

    requires s0.stack[5] == 0x1238

    requires s0.stack[8] == 0x9c1

    requires s0.stack[12] == 0x698

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x120b;
      assert s1.Peek(5) == 0x1238;
      assert s1.Peek(8) == 0x9c1;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x120b;
      assert s11.Peek(6) == 0x1238;
      assert s11.Peek(9) == 0x9c1;
      assert s11.Peek(13) == 0x698;
      assert s11.Peek(17) == 0x22d;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s15, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 249
    * Starting at 0x120b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x1238

    requires s0.stack[6] == 0x9c1

    requires s0.stack[10] == 0x698

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1238;
      assert s1.Peek(6) == 0x9c1;
      assert s1.Peek(10) == 0x698;
      assert s1.Peek(14) == 0x22d;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1216);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x11b1);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 247
    * Starting at 0x11b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x1216

    requires s0.stack[4] == 0x1238

    requires s0.stack[7] == 0x9c1

    requires s0.stack[11] == 0x698

    requires s0.stack[15] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1216;
      assert s1.Peek(4) == 0x1238;
      assert s1.Peek(7) == 0x9c1;
      assert s1.Peek(11) == 0x698;
      assert s1.Peek(15) == 0x22d;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1216;
      assert s11.Peek(4) == 0x1238;
      assert s11.Peek(7) == 0x9c1;
      assert s11.Peek(11) == 0x698;
      assert s11.Peek(15) == 0x22d;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s13, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 250
    * Starting at 0x1216
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1238

    requires s0.stack[5] == 0x9c1

    requires s0.stack[9] == 0x698

    requires s0.stack[13] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1238;
      assert s1.Peek(5) == 0x9c1;
      assert s1.Peek(9) == 0x698;
      assert s1.Peek(13) == 0x22d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s10, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 252
    * Starting at 0x1238
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1238 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9c1

    requires s0.stack[7] == 0x698

    requires s0.stack[11] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9c1;
      assert s1.Peek(7) == 0x698;
      assert s1.Peek(11) == 0x22d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s7, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 122
    * Starting at 0x9c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x698

    requires s0.stack[8] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x698;
      assert s1.Peek(8) == 0x22d;
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

  /** Node 94
    * Segment Id for this node is: 123
    * Starting at 0x9ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x698

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x698;
      assert s1.Peek(7) == 0x22d;
      var s2 := Push2(s1, 0x09d5);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b63);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s7, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 132
    * Starting at 0xb63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x9d5

    requires s0.stack[7] == 0x698

    requires s0.stack[11] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9d5;
      assert s1.Peek(7) == 0x698;
      assert s1.Peek(11) == 0x22d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 124
    * Starting at 0x9d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x698

    requires s0.stack[7] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x698;
      assert s1.Peek(7) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x698;
      assert s11.Peek(10) == 0x22d;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x698;
      assert s21.Peek(9) == 0x22d;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0a58);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s29, gas - 1)
      else
        ExecuteFromCFGNode_s97(s29, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 125
    * Starting at 0xa1e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x698

    requires s0.stack[8] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x698;
      assert s1.Peek(9) == 0x22d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a4f);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12af);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s11, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 257
    * Starting at 0x12af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xa4f

    requires s0.stack[6] == 0x698

    requires s0.stack[10] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa4f;
      assert s1.Peek(6) == 0x698;
      assert s1.Peek(10) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xa4f;
      assert s11.Peek(9) == 0x698;
      assert s11.Peek(13) == 0x22d;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12c6);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x128d);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s18, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 254
    * Starting at 0x128d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x12c6

    requires s0.stack[4] == 0xa4f

    requires s0.stack[9] == 0x698

    requires s0.stack[13] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12c6;
      assert s1.Peek(4) == 0xa4f;
      assert s1.Peek(9) == 0x698;
      assert s1.Peek(13) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1299);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s7, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1299

    requires s0.stack[5] == 0x12c6

    requires s0.stack[8] == 0xa4f

    requires s0.stack[13] == 0x698

    requires s0.stack[17] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1299;
      assert s1.Peek(5) == 0x12c6;
      assert s1.Peek(8) == 0xa4f;
      assert s1.Peek(13) == 0x698;
      assert s1.Peek(17) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1299;
      assert s11.Peek(6) == 0x12c6;
      assert s11.Peek(9) == 0xa4f;
      assert s11.Peek(14) == 0x698;
      assert s11.Peek(18) == 0x22d;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s15, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 255
    * Starting at 0x1299
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x12c6

    requires s0.stack[6] == 0xa4f

    requires s0.stack[11] == 0x698

    requires s0.stack[15] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12c6;
      assert s1.Peek(6) == 0xa4f;
      assert s1.Peek(11) == 0x698;
      assert s1.Peek(15) == 0x22d;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x12a4);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x123f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s7, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 253
    * Starting at 0x123f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x12a4

    requires s0.stack[4] == 0x12c6

    requires s0.stack[7] == 0xa4f

    requires s0.stack[12] == 0x698

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12a4;
      assert s1.Peek(4) == 0x12c6;
      assert s1.Peek(7) == 0xa4f;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x12a4;
      assert s11.Peek(4) == 0x12c6;
      assert s11.Peek(7) == 0xa4f;
      assert s11.Peek(12) == 0x698;
      assert s11.Peek(16) == 0x22d;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s13, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 256
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x12c6

    requires s0.stack[5] == 0xa4f

    requires s0.stack[10] == 0x698

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12c6;
      assert s1.Peek(5) == 0xa4f;
      assert s1.Peek(10) == 0x698;
      assert s1.Peek(14) == 0x22d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s10, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 258
    * Starting at 0x12c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa4f

    requires s0.stack[8] == 0x698

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa4f;
      assert s1.Peek(8) == 0x698;
      assert s1.Peek(12) == 0x22d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s7, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 126
    * Starting at 0xa4f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x698

    requires s0.stack[9] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x698;
      assert s1.Peek(9) == 0x22d;
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
    * Segment Id for this node is: 127
    * Starting at 0xa58
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x698

    requires s0.stack[8] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x698;
      assert s1.Peek(8) == 0x22d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push0(s4);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x698;
      assert s11.Peek(12) == 0x22d;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x698;
      assert s21.Peek(11) == 0x22d;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup2(s26);
      var s28 := Push0(s27);
      var s29 := Dup1(s28);
      var s30 := Dup6(s29);
      var s31 := Push20(s30, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s31.Peek(9) == 0x698;
      assert s31.Peek(13) == 0x22d;
      var s32 := And(s31);
      var s33 := Push20(s32, 0xffffffffffffffffffffffffffffffffffffffff);
      var s34 := And(s33);
      var s35 := Dup2(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Dup2(s39);
      var s41 := MStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s107(s41, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 128
    * Starting at 0xad4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x698

    requires s0.stack[10] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x698;
      assert s1.Peek(11) == 0x22d;
      var s2 := Add(s1);
      var s3 := Push0(s2);
      var s4 := Keccak256(s3);
      var s5 := Push0(s4);
      var s6 := Dup3(s5);
      var s7 := Dup3(s6);
      var s8 := SLoad(s7);
      var s9 := Push2(s8, 0x0ae6);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xae6;
      assert s11.Peek(10) == 0x698;
      assert s11.Peek(14) == 0x22d;
      var s12 := Push2(s11, 0x0f46);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s13, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 217
    * Starting at 0xf46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xae6

    requires s0.stack[10] == 0x698

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xae6;
      assert s1.Peek(10) == 0x698;
      assert s1.Peek(14) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f50);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s6, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf50

    requires s0.stack[5] == 0xae6

    requires s0.stack[13] == 0x698

    requires s0.stack[17] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf50;
      assert s1.Peek(5) == 0xae6;
      assert s1.Peek(13) == 0x698;
      assert s1.Peek(17) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s9, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 218
    * Starting at 0xf50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xae6

    requires s0.stack[12] == 0x698

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0f5b);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0c75);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s7, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xf5b

    requires s0.stack[5] == 0xae6

    requires s0.stack[13] == 0x698

    requires s0.stack[17] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf5b;
      assert s1.Peek(5) == 0xae6;
      assert s1.Peek(13) == 0x698;
      assert s1.Peek(17) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s9, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 219
    * Starting at 0xf5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0xae6

    requires s0.stack[12] == 0x698

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xae6;
      assert s11.Peek(12) == 0x698;
      assert s11.Peek(16) == 0x22d;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0f73);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s14, gas - 1)
      else
        ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 220
    * Starting at 0xf6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xae6

    requires s0.stack[11] == 0x698

    requires s0.stack[15] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f72);
      assert s1.Peek(0) == 0xf72;
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Push2(s1, 0x0f19);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s3, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 216
    * Starting at 0xf19
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xf72

    requires s0.stack[4] == 0xae6

    requires s0.stack[12] == 0x698

    requires s0.stack[16] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf72;
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x698;
      assert s1.Peek(16) == 0x22d;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 115
    * Segment Id for this node is: 222
    * Starting at 0xf73
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xae6

    requires s0.stack[11] == 0x698

    requires s0.stack[15] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xae6;
      assert s1.Peek(11) == 0x698;
      assert s1.Peek(15) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s6, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 129
    * Starting at 0xae6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x698

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x698;
      assert s1.Peek(12) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(5) == 0x698;
      assert s11.Peek(9) == 0x22d;
      var s12 := Dup5(s11);
      var s13 := Push20(s12, 0xffffffffffffffffffffffffffffffffffffffff);
      var s14 := And(s13);
      var s15 := Push32(s14, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := MLoad(s17);
      var s19 := Push2(s18, 0x0b4a);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0xb4a;
      assert s21.Peek(10) == 0x698;
      assert s21.Peek(14) == 0x22d;
      var s22 := Push2(s21, 0x0d28);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s23, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xb4a

    requires s0.stack[10] == 0x698

    requires s0.stack[14] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb4a;
      assert s1.Peek(10) == 0x698;
      assert s1.Peek(14) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0xb4a;
      assert s11.Peek(13) == 0x698;
      assert s11.Peek(17) == 0x22d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s14, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0xb4a

    requires s0.stack[14] == 0x698

    requires s0.stack[18] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0xb4a;
      assert s1.Peek(14) == 0x698;
      assert s1.Peek(18) == 0x22d;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s5, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0xb4a

    requires s0.stack[16] == 0x698

    requires s0.stack[20] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0xb4a;
      assert s1.Peek(16) == 0x698;
      assert s1.Peek(20) == 0x22d;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s9, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0xb4a

    requires s0.stack[15] == 0x698

    requires s0.stack[19] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0xb4a;
      assert s1.Peek(15) == 0x698;
      assert s1.Peek(19) == 0x22d;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s6, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xb4a

    requires s0.stack[11] == 0x698

    requires s0.stack[15] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb4a;
      assert s1.Peek(11) == 0x698;
      assert s1.Peek(15) == 0x22d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s6, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 130
    * Starting at 0xb4a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x698

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x698;
      assert s1.Peek(12) == 0x22d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0b5d);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0xb5d;
      assert s11.Peek(7) == 0x698;
      assert s11.Peek(11) == 0x22d;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0b68);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s14, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 133
    * Starting at 0xb68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xb5d

    requires s0.stack[8] == 0x698

    requires s0.stack[12] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb5d;
      assert s1.Peek(8) == 0x698;
      assert s1.Peek(12) == 0x22d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s5, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 131
    * Starting at 0xb5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x698

    requires s0.stack[8] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x698;
      assert s1.Peek(8) == 0x22d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s6, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 104
    * Starting at 0x698
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x698 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x22d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22d;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s9, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 51
    * Starting at 0x22d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x023a);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d00);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s8, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 174
    * Starting at 0xd00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x23a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x23a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d13);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd13;
      assert s11.Peek(5) == 0x23a;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0cf1);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s14, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 172
    * Starting at 0xcf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd13

    requires s0.stack[6] == 0x23a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd13;
      assert s1.Peek(6) == 0x23a;
      var s2 := Push2(s1, 0x0cfa);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0ce6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s5, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 171
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcfa

    requires s0.stack[4] == 0xd13

    requires s0.stack[8] == 0x23a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcfa;
      assert s1.Peek(4) == 0xd13;
      assert s1.Peek(8) == 0x23a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s11, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 173
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd13

    requires s0.stack[7] == 0x23a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd13;
      assert s1.Peek(7) == 0x23a;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s6, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 175
    * Starting at 0xd13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x23a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x23a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s6, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 52
    * Starting at 0x23a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23a as nat
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
    * Segment Id for this node is: 46
    * Starting at 0x1f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01fd);
      var s3 := Push2(s2, 0x05f5);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s4, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 93
    * Starting at 0x5f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fd;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0604);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0e5b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s9, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 204
    * Starting at 0xe5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x604

    requires s0.stack[4] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x604;
      assert s1.Peek(4) == 0x1fd;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x604;
      assert s11.Peek(7) == 0x1fd;
      var s12 := Push2(s11, 0x0e72);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s13, gas - 1)
      else
        ExecuteFromCFGNode_s136(s13, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 205
    * Starting at 0xe6c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x604

    requires s0.stack[6] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x604;
      assert s1.Peek(7) == 0x1fd;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s137(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 206
    * Starting at 0xe72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x604

    requires s0.stack[6] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x604;
      assert s1.Peek(6) == 0x1fd;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0e85);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s8, gas - 1)
      else
        ExecuteFromCFGNode_s138(s8, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 207
    * Starting at 0xe7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x604

    requires s0.stack[6] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e84);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x604;
      assert s1.Peek(7) == 0x1fd;
      var s2 := Push2(s1, 0x0e2e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s3, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 203
    * Starting at 0xe2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xe84

    requires s0.stack[4] == 0x604

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x604;
      assert s1.Peek(7) == 0x1fd;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 140
    * Segment Id for this node is: 209
    * Starting at 0xe85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x604

    requires s0.stack[6] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x604;
      assert s1.Peek(6) == 0x1fd;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s6, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 94
    * Starting at 0x604
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x604 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1fd;
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
      assert s11.Peek(4) == 0x1fd;
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
      assert s21.Peek(5) == 0x1fd;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x0630);
      assert s31.Peek(0) == 0x630;
      assert s31.Peek(8) == 0x1fd;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0e5b);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s34, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 204
    * Starting at 0xe5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x630

    requires s0.stack[8] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x630;
      assert s1.Peek(8) == 0x1fd;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x630;
      assert s11.Peek(11) == 0x1fd;
      var s12 := Push2(s11, 0x0e72);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s13, gas - 1)
      else
        ExecuteFromCFGNode_s143(s13, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 205
    * Starting at 0xe6c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x630

    requires s0.stack[10] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x630;
      assert s1.Peek(11) == 0x1fd;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s144(s5, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 206
    * Starting at 0xe72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x630

    requires s0.stack[10] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x630;
      assert s1.Peek(10) == 0x1fd;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0e85);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s8, gas - 1)
      else
        ExecuteFromCFGNode_s145(s8, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 207
    * Starting at 0xe7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x630

    requires s0.stack[10] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e84);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x630;
      assert s1.Peek(11) == 0x1fd;
      var s2 := Push2(s1, 0x0e2e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s3, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 203
    * Starting at 0xe2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xe84

    requires s0.stack[4] == 0x630

    requires s0.stack[11] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x630;
      assert s1.Peek(11) == 0x1fd;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 147
    * Segment Id for this node is: 209
    * Starting at 0xe85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x630

    requires s0.stack[10] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x630;
      assert s1.Peek(10) == 0x1fd;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s6, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 95
    * Starting at 0x630
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x630 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1fd;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x067b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s5, gas - 1)
      else
        ExecuteFromCFGNode_s149(s5, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 96
    * Starting at 0x637
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x637 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x1fd;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0652);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s5, gas - 1)
      else
        ExecuteFromCFGNode_s150(s5, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 97
    * Starting at 0x63f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x1fd;
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
      assert s11.Peek(7) == 0x1fd;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x067b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s14, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 101
    * Starting at 0x67b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1fd;
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
      ExecuteFromCFGNode_s152(s10, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 47
    * Starting at 0x1fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x020a);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0bf7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s8, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 146
    * Starting at 0xbf7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0x20a;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0c0f);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0bbf);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s19, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 141
    * Starting at 0xbbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xc0f

    requires s0.stack[6] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc0f;
      assert s1.Peek(6) == 0x20a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0bc9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0b6d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s6, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 134
    * Starting at 0xb6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbc9

    requires s0.stack[5] == 0xc0f

    requires s0.stack[9] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbc9;
      assert s1.Peek(5) == 0xc0f;
      assert s1.Peek(9) == 0x20a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s10, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 142
    * Starting at 0xbc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xc0f

    requires s0.stack[8] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc0f;
      assert s1.Peek(8) == 0x20a;
      var s2 := Push2(s1, 0x0bd3);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0b77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s6, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xbd3

    requires s0.stack[7] == 0xc0f

    requires s0.stack[11] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbd3;
      assert s1.Peek(7) == 0xc0f;
      assert s1.Peek(11) == 0x20a;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xbd3;
      assert s11.Peek(8) == 0xc0f;
      assert s11.Peek(12) == 0x20a;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s15, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 143
    * Starting at 0xbd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xc0f

    requires s0.stack[9] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc0f;
      assert s1.Peek(9) == 0x20a;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0be3);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0b87);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s11, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 136
    * Starting at 0xb87
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xbe3

    requires s0.stack[8] == 0xc0f

    requires s0.stack[12] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbe3;
      assert s1.Peek(8) == 0xc0f;
      assert s1.Peek(12) == 0x20a;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s160(s2, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 137
    * Starting at 0xb89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbe3

    requires s0.stack[9] == 0xc0f

    requires s0.stack[13] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbe3;
      assert s1.Peek(9) == 0xc0f;
      assert s1.Peek(13) == 0x20a;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ba4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s7, gas - 1)
      else
        ExecuteFromCFGNode_s161(s7, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 138
    * Starting at 0xb92
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbe3

    requires s0.stack[9] == 0xc0f

    requires s0.stack[13] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xbe3;
      assert s1.Peek(10) == 0xc0f;
      assert s1.Peek(14) == 0x20a;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xbe3;
      assert s11.Peek(10) == 0xc0f;
      assert s11.Peek(14) == 0x20a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0b89);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s15, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 139
    * Starting at 0xba4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbe3

    requires s0.stack[9] == 0xc0f

    requires s0.stack[13] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbe3;
      assert s1.Peek(9) == 0xc0f;
      assert s1.Peek(13) == 0x20a;
      var s2 := Push0(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s11, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 144
    * Starting at 0xbe3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xc0f

    requires s0.stack[8] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc0f;
      assert s1.Peek(8) == 0x20a;
      var s2 := Push2(s1, 0x0bec);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0baf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s5, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 140
    * Starting at 0xbaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xbec

    requires s0.stack[6] == 0xc0f

    requires s0.stack[10] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbec;
      assert s1.Peek(6) == 0xc0f;
      assert s1.Peek(10) == 0x20a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xbec;
      assert s11.Peek(7) == 0xc0f;
      assert s11.Peek(11) == 0x20a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s14, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 145
    * Starting at 0xbec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xc0f

    requires s0.stack[9] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc0f;
      assert s1.Peek(9) == 0x20a;
      var s2 := Dup5(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s11, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 147
    * Starting at 0xc0f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s8, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 48
    * Starting at 0x20a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20a as nat
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

  /** Node 168
    * Segment Id for this node is: 98
    * Starting at 0x652
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1fd;
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
      ExecuteFromCFGNode_s169(s11, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 99
    * Starting at 0x65e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1fd;
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
      assert s11.Peek(7) == 0x1fd;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x065e);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s16, gas - 1)
      else
        ExecuteFromCFGNode_s170(s16, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 100
    * Starting at 0x672
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x672 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1fd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x1fd;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s151(s8, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 42
    * Starting at 0x1c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01df);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01da);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1da;
      assert s11.Peek(3) == 0x1df;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ca8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s14, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 165
    * Starting at 0xca8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1da

    requires s0.stack[3] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1da;
      assert s1.Peek(3) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cbe);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s11, gas - 1)
      else
        ExecuteFromCFGNode_s173(s11, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 166
    * Starting at 0xcb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1da

    requires s0.stack[5] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0cbd);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0x1da;
      assert s1.Peek(6) == 0x1df;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s3, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xcbd

    requires s0.stack[5] == 0x1da

    requires s0.stack[6] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0x1da;
      assert s1.Peek(6) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 175
    * Segment Id for this node is: 168
    * Starting at 0xcbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1da

    requires s0.stack[5] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1da;
      assert s1.Peek(5) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ccb);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s9, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xccb

    requires s0.stack[8] == 0x1da

    requires s0.stack[9] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xccb;
      assert s1.Peek(8) == 0x1da;
      assert s1.Peek(9) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s10, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x1da

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0x1da;
      assert s1.Peek(12) == 0x1df;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s5, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xccb

    requires s0.stack[13] == 0x1da

    requires s0.stack[14] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xccb;
      assert s1.Peek(13) == 0x1da;
      assert s1.Peek(14) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xccb

    requires s0.stack[16] == 0x1da

    requires s0.stack[17] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xccb;
      assert s1.Peek(16) == 0x1da;
      assert s1.Peek(17) == 0x1df;
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
      ExecuteFromCFGNode_s180(s11, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xccb

    requires s0.stack[15] == 0x1da

    requires s0.stack[16] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xccb;
      assert s1.Peek(15) == 0x1da;
      assert s1.Peek(16) == 0x1df;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s7, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xccb

    requires s0.stack[12] == 0x1da

    requires s0.stack[13] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0x1da;
      assert s1.Peek(13) == 0x1df;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s5, gas - 1)
      else
        ExecuteFromCFGNode_s182(s5, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x1da

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0x1da;
      assert s1.Peek(13) == 0x1df;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 183
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x1da

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0x1da;
      assert s1.Peek(12) == 0x1df;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s3, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xccb

    requires s0.stack[9] == 0x1da

    requires s0.stack[10] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xccb;
      assert s1.Peek(9) == 0x1da;
      assert s1.Peek(10) == 0x1df;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 169
    * Starting at 0xccb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1da

    requires s0.stack[7] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1da;
      assert s1.Peek(7) == 0x1df;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0cdc);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c94);
      assert s11.Peek(0) == 0xc94;
      assert s11.Peek(3) == 0xcdc;
      assert s11.Peek(9) == 0x1da;
      assert s11.Peek(10) == 0x1df;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s12, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 163
    * Starting at 0xc94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xcdc

    requires s0.stack[8] == 0x1da

    requires s0.stack[9] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcdc;
      assert s1.Peek(8) == 0x1da;
      assert s1.Peek(9) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ca2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c7e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s10, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 159
    * Starting at 0xc7e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x1da

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0x1da;
      assert s1.Peek(12) == 0x1df;
      var s2 := Push2(s1, 0x0c87);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s5, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc87

    requires s0.stack[3] == 0xca2

    requires s0.stack[7] == 0xcdc

    requires s0.stack[13] == 0x1da

    requires s0.stack[14] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc87;
      assert s1.Peek(3) == 0xca2;
      assert s1.Peek(7) == 0xcdc;
      assert s1.Peek(13) == 0x1da;
      assert s1.Peek(14) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s9, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 160
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xca2

    requires s0.stack[6] == 0xcdc

    requires s0.stack[12] == 0x1da

    requires s0.stack[13] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0x1da;
      assert s1.Peek(13) == 0x1df;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c91);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s5, gas - 1)
      else
        ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 161
    * Starting at 0xc8e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x1da

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0x1da;
      assert s1.Peek(13) == 0x1df;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 191
    * Segment Id for this node is: 162
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x1da

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0x1da;
      assert s1.Peek(12) == 0x1df;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s3, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 164
    * Starting at 0xca2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xcdc

    requires s0.stack[9] == 0x1da

    requires s0.stack[10] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcdc;
      assert s1.Peek(9) == 0x1da;
      assert s1.Peek(10) == 0x1df;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s6, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 170
    * Starting at 0xcdc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1da

    requires s0.stack[7] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1da;
      assert s1.Peek(7) == 0x1df;
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
      ExecuteFromCFGNode_s194(s10, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 43
    * Starting at 0x1da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1df;
      var s2 := Push2(s1, 0x050f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s3, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 85
    * Starting at 0x50f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push0(s4);
      var s6 := Push2(s5, 0x051c);
      var s7 := Push2(s6, 0x0724);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s8, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x51c

    requires s0.stack[7] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x51c;
      assert s1.Peek(7) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s7, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 86
    * Starting at 0x51c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1df;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x1df;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push0(s14);
      var s16 := Keccak256(s15);
      var s17 := Push0(s16);
      var s18 := Dup6(s17);
      var s19 := Push20(s18, 0xffffffffffffffffffffffffffffffffffffffff);
      var s20 := And(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(8) == 0x1df;
      var s22 := And(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Add(s25);
      var s27 := Swap1(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x1df;
      var s32 := Push0(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Pop(s35);
      var s37 := Dup3(s36);
      var s38 := Dup2(s37);
      var s39 := Lt(s38);
      var s40 := IsZero(s39);
      var s41 := Push2(s40, 0x05d6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s198(s41, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 87
    * Starting at 0x59b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x5d6

    requires s0.stack[6] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpI(s0);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s0.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s1, gas - 1)
      else
        ExecuteFromCFGNode_s199(s1, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 88
    * Starting at 0x59c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x1df;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x05cd);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0fe9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s11, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 227
    * Starting at 0xfe9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x5cd

    requires s0.stack[6] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5cd;
      assert s1.Peek(6) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x5cd;
      assert s11.Peek(9) == 0x1df;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1000);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0fc7);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s18, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 224
    * Starting at 0xfc7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1000

    requires s0.stack[4] == 0x5cd

    requires s0.stack[9] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1000;
      assert s1.Peek(4) == 0x5cd;
      assert s1.Peek(9) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0fd3);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s7, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xfd3

    requires s0.stack[5] == 0x1000

    requires s0.stack[8] == 0x5cd

    requires s0.stack[13] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xfd3;
      assert s1.Peek(5) == 0x1000;
      assert s1.Peek(8) == 0x5cd;
      assert s1.Peek(13) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xfd3;
      assert s11.Peek(6) == 0x1000;
      assert s11.Peek(9) == 0x5cd;
      assert s11.Peek(14) == 0x1df;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s15, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 225
    * Starting at 0xfd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1000

    requires s0.stack[6] == 0x5cd

    requires s0.stack[11] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1000;
      assert s1.Peek(6) == 0x5cd;
      assert s1.Peek(11) == 0x1df;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0fde);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0f79);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s7, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 223
    * Starting at 0xf79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xfde

    requires s0.stack[4] == 0x1000

    requires s0.stack[7] == 0x5cd

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfde;
      assert s1.Peek(4) == 0x1000;
      assert s1.Peek(7) == 0x5cd;
      assert s1.Peek(12) == 0x1df;
      var s2 := Push32(s1, 0x45524332303a2064656372656173656420616c6c6f77616e63652062656c6f77);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x207a65726f000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xfde;
      assert s11.Peek(4) == 0x1000;
      assert s11.Peek(7) == 0x5cd;
      assert s11.Peek(12) == 0x1df;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s13, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 226
    * Starting at 0xfde
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfde as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1000

    requires s0.stack[5] == 0x5cd

    requires s0.stack[10] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1000;
      assert s1.Peek(5) == 0x5cd;
      assert s1.Peek(10) == 0x1df;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s10, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 228
    * Starting at 0x1000
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1000 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5cd

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5cd;
      assert s1.Peek(8) == 0x1df;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s7, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 89
    * Starting at 0x5cd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1df;
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

  /** Node 208
    * Segment Id for this node is: 90
    * Starting at 0x5d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1df;
      var s2 := Push2(s1, 0x05ea);
      var s3 := Push2(s2, 0x05e1);
      var s4 := Push2(s3, 0x0724);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s5, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x5e1

    requires s0.stack[1] == 0x5ea

    requires s0.stack[6] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5e1;
      assert s1.Peek(1) == 0x5ea;
      assert s1.Peek(6) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s7, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 91
    * Starting at 0x5e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x5ea

    requires s0.stack[6] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5ea;
      assert s1.Peek(6) == 0x1df;
      var s2 := Dup6(s1);
      var s3 := Dup6(s2);
      var s4 := Dup5(s3);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x072b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s7, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 108
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5ea

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ea;
      assert s1.Peek(8) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0799);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s10, gas - 1)
      else
        ExecuteFromCFGNode_s212(s10, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 109
    * Starting at 0x75f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5ea

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5ea;
      assert s1.Peek(9) == 0x1df;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0790);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1077);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s11, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 233
    * Starting at 0x1077
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1077 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x790

    requires s0.stack[5] == 0x5ea

    requires s0.stack[10] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x790;
      assert s1.Peek(5) == 0x5ea;
      assert s1.Peek(10) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x790;
      assert s11.Peek(8) == 0x5ea;
      assert s11.Peek(13) == 0x1df;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x108e);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1055);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s18, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 230
    * Starting at 0x1055
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x108e

    requires s0.stack[4] == 0x790

    requires s0.stack[8] == 0x5ea

    requires s0.stack[13] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x108e;
      assert s1.Peek(4) == 0x790;
      assert s1.Peek(8) == 0x5ea;
      assert s1.Peek(13) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1061);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s7, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1061

    requires s0.stack[5] == 0x108e

    requires s0.stack[8] == 0x790

    requires s0.stack[12] == 0x5ea

    requires s0.stack[17] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1061;
      assert s1.Peek(5) == 0x108e;
      assert s1.Peek(8) == 0x790;
      assert s1.Peek(12) == 0x5ea;
      assert s1.Peek(17) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1061;
      assert s11.Peek(6) == 0x108e;
      assert s11.Peek(9) == 0x790;
      assert s11.Peek(13) == 0x5ea;
      assert s11.Peek(18) == 0x1df;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s15, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 231
    * Starting at 0x1061
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1061 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x108e

    requires s0.stack[6] == 0x790

    requires s0.stack[10] == 0x5ea

    requires s0.stack[15] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x108e;
      assert s1.Peek(6) == 0x790;
      assert s1.Peek(10) == 0x5ea;
      assert s1.Peek(15) == 0x1df;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1007);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s7, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 229
    * Starting at 0x1007
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1007 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x106c

    requires s0.stack[4] == 0x108e

    requires s0.stack[7] == 0x790

    requires s0.stack[11] == 0x5ea

    requires s0.stack[16] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106c;
      assert s1.Peek(4) == 0x108e;
      assert s1.Peek(7) == 0x790;
      assert s1.Peek(11) == 0x5ea;
      assert s1.Peek(16) == 0x1df;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106c;
      assert s11.Peek(4) == 0x108e;
      assert s11.Peek(7) == 0x790;
      assert s11.Peek(11) == 0x5ea;
      assert s11.Peek(16) == 0x1df;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s218(s13, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 232
    * Starting at 0x106c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x108e

    requires s0.stack[5] == 0x790

    requires s0.stack[9] == 0x5ea

    requires s0.stack[14] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x108e;
      assert s1.Peek(5) == 0x790;
      assert s1.Peek(9) == 0x5ea;
      assert s1.Peek(14) == 0x1df;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s10, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 234
    * Starting at 0x108e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x790

    requires s0.stack[7] == 0x5ea

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x790;
      assert s1.Peek(7) == 0x5ea;
      assert s1.Peek(12) == 0x1df;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s7, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 110
    * Starting at 0x790
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x790 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5ea

    requires s0.stack[9] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ea;
      assert s1.Peek(9) == 0x1df;
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

  /** Node 221
    * Segment Id for this node is: 111
    * Starting at 0x799
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5ea

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ea;
      assert s1.Peek(8) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0807);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s10, gas - 1)
      else
        ExecuteFromCFGNode_s222(s10, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 112
    * Starting at 0x7cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5ea

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5ea;
      assert s1.Peek(9) == 0x1df;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07fe);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1105);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s11, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x7fe

    requires s0.stack[5] == 0x5ea

    requires s0.stack[10] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7fe;
      assert s1.Peek(5) == 0x5ea;
      assert s1.Peek(10) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x7fe;
      assert s11.Peek(8) == 0x5ea;
      assert s11.Peek(13) == 0x1df;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x111c);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10e3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s18, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 236
    * Starting at 0x10e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x111c

    requires s0.stack[4] == 0x7fe

    requires s0.stack[8] == 0x5ea

    requires s0.stack[13] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111c;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(8) == 0x5ea;
      assert s1.Peek(13) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10ef);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s7, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x10ef

    requires s0.stack[5] == 0x111c

    requires s0.stack[8] == 0x7fe

    requires s0.stack[12] == 0x5ea

    requires s0.stack[17] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ef;
      assert s1.Peek(5) == 0x111c;
      assert s1.Peek(8) == 0x7fe;
      assert s1.Peek(12) == 0x5ea;
      assert s1.Peek(17) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x10ef;
      assert s11.Peek(6) == 0x111c;
      assert s11.Peek(9) == 0x7fe;
      assert s11.Peek(13) == 0x5ea;
      assert s11.Peek(18) == 0x1df;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s15, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 237
    * Starting at 0x10ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x111c

    requires s0.stack[6] == 0x7fe

    requires s0.stack[10] == 0x5ea

    requires s0.stack[15] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x111c;
      assert s1.Peek(6) == 0x7fe;
      assert s1.Peek(10) == 0x5ea;
      assert s1.Peek(15) == 0x1df;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10fa);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1095);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s7, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 235
    * Starting at 0x1095
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1095 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x10fa

    requires s0.stack[4] == 0x111c

    requires s0.stack[7] == 0x7fe

    requires s0.stack[11] == 0x5ea

    requires s0.stack[16] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10fa;
      assert s1.Peek(4) == 0x111c;
      assert s1.Peek(7) == 0x7fe;
      assert s1.Peek(11) == 0x5ea;
      assert s1.Peek(16) == 0x1df;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10fa;
      assert s11.Peek(4) == 0x111c;
      assert s11.Peek(7) == 0x7fe;
      assert s11.Peek(11) == 0x5ea;
      assert s11.Peek(16) == 0x1df;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s13, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 238
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x111c

    requires s0.stack[5] == 0x7fe

    requires s0.stack[9] == 0x5ea

    requires s0.stack[14] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111c;
      assert s1.Peek(5) == 0x7fe;
      assert s1.Peek(9) == 0x5ea;
      assert s1.Peek(14) == 0x1df;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s10, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 240
    * Starting at 0x111c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x7fe

    requires s0.stack[7] == 0x5ea

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7fe;
      assert s1.Peek(7) == 0x5ea;
      assert s1.Peek(12) == 0x1df;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s7, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 113
    * Starting at 0x7fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x5ea

    requires s0.stack[9] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5ea;
      assert s1.Peek(9) == 0x1df;
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

  /** Node 231
    * Segment Id for this node is: 114
    * Starting at 0x807
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5ea

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5ea;
      assert s1.Peek(8) == 0x1df;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x5ea;
      assert s11.Peek(11) == 0x1df;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x5ea;
      assert s21.Peek(11) == 0x1df;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x5ea;
      assert s31.Peek(11) == 0x1df;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s232(s41, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 115
    * Starting at 0x885
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x885 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x5ea

    requires s0.stack[8] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x5ea;
      assert s1.Peek(9) == 0x1df;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(9) == 0x5ea;
      assert s11.Peek(14) == 0x1df;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0d28);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s15, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x8e1

    requires s0.stack[9] == 0x5ea

    requires s0.stack[14] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e1;
      assert s1.Peek(9) == 0x5ea;
      assert s1.Peek(14) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x8e1;
      assert s11.Peek(12) == 0x5ea;
      assert s11.Peek(17) == 0x1df;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s14, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x8e1

    requires s0.stack[13] == 0x5ea

    requires s0.stack[18] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x8e1;
      assert s1.Peek(13) == 0x5ea;
      assert s1.Peek(18) == 0x1df;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s5, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x8e1

    requires s0.stack[15] == 0x5ea

    requires s0.stack[20] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x8e1;
      assert s1.Peek(15) == 0x5ea;
      assert s1.Peek(20) == 0x1df;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s9, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x8e1

    requires s0.stack[14] == 0x5ea

    requires s0.stack[19] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x8e1;
      assert s1.Peek(14) == 0x5ea;
      assert s1.Peek(19) == 0x1df;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s6, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x8e1

    requires s0.stack[10] == 0x5ea

    requires s0.stack[15] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e1;
      assert s1.Peek(10) == 0x5ea;
      assert s1.Peek(15) == 0x1df;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s6, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 116
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x5ea

    requires s0.stack[12] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5ea;
      assert s1.Peek(12) == 0x1df;
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
      assert s11.Peek(0) == 0x5ea;
      assert s11.Peek(5) == 0x1df;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s12, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 92
    * Starting at 0x5ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1df

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1df;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s10, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 44
    * Starting at 0x1df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01ec);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d00);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s8, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 174
    * Starting at 0xd00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1ec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ec;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d13);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd13;
      assert s11.Peek(5) == 0x1ec;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0cf1);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s14, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 172
    * Starting at 0xcf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd13

    requires s0.stack[6] == 0x1ec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd13;
      assert s1.Peek(6) == 0x1ec;
      var s2 := Push2(s1, 0x0cfa);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0ce6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s5, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 171
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcfa

    requires s0.stack[4] == 0xd13

    requires s0.stack[8] == 0x1ec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcfa;
      assert s1.Peek(4) == 0xd13;
      assert s1.Peek(8) == 0x1ec;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s11, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 173
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd13

    requires s0.stack[7] == 0x1ec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd13;
      assert s1.Peek(7) == 0x1ec;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s6, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 175
    * Starting at 0xd13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1ec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ec;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s6, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 45
    * Starting at 0x1ec
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ec as nat
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

  /** Node 247
    * Segment Id for this node is: 38
    * Starting at 0x195
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x195 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01af);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x01aa);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x1aa;
      assert s11.Peek(3) == 0x1af;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0dc5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s14, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 192
    * Starting at 0xdc5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1aa

    requires s0.stack[3] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1aa;
      assert s1.Peek(3) == 0x1af;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0dda);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s10, gas - 1)
      else
        ExecuteFromCFGNode_s249(s10, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 193
    * Starting at 0xdd2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1aa

    requires s0.stack[4] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0dd9);
      assert s1.Peek(0) == 0xdd9;
      assert s1.Peek(4) == 0x1aa;
      assert s1.Peek(5) == 0x1af;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s3, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0xdd9

    requires s0.stack[4] == 0x1aa

    requires s0.stack[5] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xdd9;
      assert s1.Peek(4) == 0x1aa;
      assert s1.Peek(5) == 0x1af;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 251
    * Segment Id for this node is: 195
    * Starting at 0xdda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1aa

    requires s0.stack[4] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1aa;
      assert s1.Peek(4) == 0x1af;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0de7);
      var s4 := Dup5(s3);
      var s5 := Dup3(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s9, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xde7

    requires s0.stack[7] == 0x1aa

    requires s0.stack[8] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde7;
      assert s1.Peek(7) == 0x1aa;
      assert s1.Peek(8) == 0x1af;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s10, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xde7

    requires s0.stack[10] == 0x1aa

    requires s0.stack[11] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xde7;
      assert s1.Peek(10) == 0x1aa;
      assert s1.Peek(11) == 0x1af;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s5, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xde7

    requires s0.stack[12] == 0x1aa

    requires s0.stack[13] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xde7;
      assert s1.Peek(12) == 0x1aa;
      assert s1.Peek(13) == 0x1af;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s6, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xde7

    requires s0.stack[15] == 0x1aa

    requires s0.stack[16] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xde7;
      assert s1.Peek(15) == 0x1aa;
      assert s1.Peek(16) == 0x1af;
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
      ExecuteFromCFGNode_s256(s11, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xde7

    requires s0.stack[14] == 0x1aa

    requires s0.stack[15] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xde7;
      assert s1.Peek(14) == 0x1aa;
      assert s1.Peek(15) == 0x1af;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s7, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xde7

    requires s0.stack[11] == 0x1aa

    requires s0.stack[12] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xde7;
      assert s1.Peek(11) == 0x1aa;
      assert s1.Peek(12) == 0x1af;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s5, gas - 1)
      else
        ExecuteFromCFGNode_s258(s5, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xde7

    requires s0.stack[10] == 0x1aa

    requires s0.stack[11] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xde7;
      assert s1.Peek(11) == 0x1aa;
      assert s1.Peek(12) == 0x1af;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 259
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xde7

    requires s0.stack[10] == 0x1aa

    requires s0.stack[11] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xde7;
      assert s1.Peek(10) == 0x1aa;
      assert s1.Peek(11) == 0x1af;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s3, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xde7

    requires s0.stack[8] == 0x1aa

    requires s0.stack[9] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde7;
      assert s1.Peek(8) == 0x1aa;
      assert s1.Peek(9) == 0x1af;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s6, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 196
    * Starting at 0xde7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1aa

    requires s0.stack[6] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1aa;
      assert s1.Peek(6) == 0x1af;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s9, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 39
    * Starting at 0x1aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1af;
      var s2 := Push2(s1, 0x04ca);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s3, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 84
    * Starting at 0x4ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1af

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1af;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x1af;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(3) == 0x1af;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Swap2(s23);
      var s25 := Swap1(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s27, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 40
    * Starting at 0x1af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x01bc);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d28);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s8, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1bc;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x1bc;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s14, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x1bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x1bc;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s5, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x1bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x1bc;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s9, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x1bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x1bc;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s6, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1bc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s6, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 41
    * Starting at 0x1bc
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bc as nat
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

  /** Node 271
    * Segment Id for this node is: 34
    * Starting at 0x165
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x017f);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x017a);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x17a;
      assert s11.Peek(3) == 0x17f;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ca8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s14, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 165
    * Starting at 0xca8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x17a

    requires s0.stack[3] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x17a;
      assert s1.Peek(3) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cbe);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s275(s11, gas - 1)
      else
        ExecuteFromCFGNode_s273(s11, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 166
    * Starting at 0xcb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x17a

    requires s0.stack[5] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0cbd);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0x17a;
      assert s1.Peek(6) == 0x17f;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s3, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xcbd

    requires s0.stack[5] == 0x17a

    requires s0.stack[6] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0x17a;
      assert s1.Peek(6) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 275
    * Segment Id for this node is: 168
    * Starting at 0xcbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x17a

    requires s0.stack[5] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x17a;
      assert s1.Peek(5) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ccb);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s9, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xccb

    requires s0.stack[8] == 0x17a

    requires s0.stack[9] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xccb;
      assert s1.Peek(8) == 0x17a;
      assert s1.Peek(9) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s10, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x17a

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0x17a;
      assert s1.Peek(12) == 0x17f;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s278(s5, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xccb

    requires s0.stack[13] == 0x17a

    requires s0.stack[14] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xccb;
      assert s1.Peek(13) == 0x17a;
      assert s1.Peek(14) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s6, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xccb

    requires s0.stack[16] == 0x17a

    requires s0.stack[17] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xccb;
      assert s1.Peek(16) == 0x17a;
      assert s1.Peek(17) == 0x17f;
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
      ExecuteFromCFGNode_s280(s11, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xccb

    requires s0.stack[15] == 0x17a

    requires s0.stack[16] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xccb;
      assert s1.Peek(15) == 0x17a;
      assert s1.Peek(16) == 0x17f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s7, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xccb

    requires s0.stack[12] == 0x17a

    requires s0.stack[13] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0x17a;
      assert s1.Peek(13) == 0x17f;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s283(s5, gas - 1)
      else
        ExecuteFromCFGNode_s282(s5, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x17a

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0x17a;
      assert s1.Peek(13) == 0x17f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 283
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0x17a

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0x17a;
      assert s1.Peek(12) == 0x17f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s3, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xccb

    requires s0.stack[9] == 0x17a

    requires s0.stack[10] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xccb;
      assert s1.Peek(9) == 0x17a;
      assert s1.Peek(10) == 0x17f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s6, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 169
    * Starting at 0xccb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x17a

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x17a;
      assert s1.Peek(7) == 0x17f;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0cdc);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c94);
      assert s11.Peek(0) == 0xc94;
      assert s11.Peek(3) == 0xcdc;
      assert s11.Peek(9) == 0x17a;
      assert s11.Peek(10) == 0x17f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s12, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 163
    * Starting at 0xc94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xcdc

    requires s0.stack[8] == 0x17a

    requires s0.stack[9] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcdc;
      assert s1.Peek(8) == 0x17a;
      assert s1.Peek(9) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ca2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c7e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s10, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 159
    * Starting at 0xc7e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x17a

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0x17a;
      assert s1.Peek(12) == 0x17f;
      var s2 := Push2(s1, 0x0c87);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s5, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc87

    requires s0.stack[3] == 0xca2

    requires s0.stack[7] == 0xcdc

    requires s0.stack[13] == 0x17a

    requires s0.stack[14] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc87;
      assert s1.Peek(3) == 0xca2;
      assert s1.Peek(7) == 0xcdc;
      assert s1.Peek(13) == 0x17a;
      assert s1.Peek(14) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s9, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 160
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xca2

    requires s0.stack[6] == 0xcdc

    requires s0.stack[12] == 0x17a

    requires s0.stack[13] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0x17a;
      assert s1.Peek(13) == 0x17f;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c91);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s5, gas - 1)
      else
        ExecuteFromCFGNode_s290(s5, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 161
    * Starting at 0xc8e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x17a

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0x17a;
      assert s1.Peek(13) == 0x17f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 291
    * Segment Id for this node is: 162
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0x17a

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0x17a;
      assert s1.Peek(12) == 0x17f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s3, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 164
    * Starting at 0xca2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xcdc

    requires s0.stack[9] == 0x17a

    requires s0.stack[10] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcdc;
      assert s1.Peek(9) == 0x17a;
      assert s1.Peek(10) == 0x17f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s6, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 170
    * Starting at 0xcdc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x17a

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x17a;
      assert s1.Peek(7) == 0x17f;
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
      ExecuteFromCFGNode_s294(s10, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 35
    * Starting at 0x17a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x17f;
      var s2 := Push2(s1, 0x0423);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s3, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 79
    * Starting at 0x423
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x423 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x04c0);
      var s4 := Push2(s3, 0x042f);
      var s5 := Push2(s4, 0x0724);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s6, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x42f

    requires s0.stack[1] == 0x4c0

    requires s0.stack[5] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x42f;
      assert s1.Peek(1) == 0x4c0;
      assert s1.Peek(5) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s7, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 80
    * Starting at 0x42f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x4c0

    requires s0.stack[5] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c0;
      assert s1.Peek(5) == 0x17f;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push0(s4);
      var s6 := Push2(s5, 0x043c);
      var s7 := Push2(s6, 0x0724);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s8, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x43c

    requires s0.stack[6] == 0x4c0

    requires s0.stack[10] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x43c;
      assert s1.Peek(6) == 0x4c0;
      assert s1.Peek(10) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s7, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 81
    * Starting at 0x43c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x4c0

    requires s0.stack[10] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x4c0;
      assert s1.Peek(10) == 0x17f;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x4c0;
      assert s11.Peek(10) == 0x17f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push0(s14);
      var s16 := Keccak256(s15);
      var s17 := Push0(s16);
      var s18 := Dup9(s17);
      var s19 := Push20(s18, 0xffffffffffffffffffffffffffffffffffffffff);
      var s20 := And(s19);
      var s21 := Push20(s20, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s21.Peek(7) == 0x4c0;
      assert s21.Peek(11) == 0x17f;
      var s22 := And(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Add(s25);
      var s27 := Swap1(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x4c0;
      assert s31.Peek(8) == 0x17f;
      var s32 := Push0(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Push2(s34, 0x04bb);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Push2(s37, 0x0f46);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s39, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 217
    * Starting at 0xf46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x4bb

    requires s0.stack[5] == 0x4c0

    requires s0.stack[9] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4bb;
      assert s1.Peek(5) == 0x4c0;
      assert s1.Peek(9) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f50);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s6, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xf50

    requires s0.stack[5] == 0x4bb

    requires s0.stack[8] == 0x4c0

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf50;
      assert s1.Peek(5) == 0x4bb;
      assert s1.Peek(8) == 0x4c0;
      assert s1.Peek(12) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s9, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 218
    * Starting at 0xf50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x4bb

    requires s0.stack[7] == 0x4c0

    requires s0.stack[11] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4bb;
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0f5b);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0c75);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s7, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xf5b

    requires s0.stack[5] == 0x4bb

    requires s0.stack[8] == 0x4c0

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf5b;
      assert s1.Peek(5) == 0x4bb;
      assert s1.Peek(8) == 0x4c0;
      assert s1.Peek(12) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s9, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 219
    * Starting at 0xf5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x4bb

    requires s0.stack[7] == 0x4c0

    requires s0.stack[11] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4bb;
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0x4bb;
      assert s11.Peek(7) == 0x4c0;
      assert s11.Peek(11) == 0x17f;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0f73);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s14, gas - 1)
      else
        ExecuteFromCFGNode_s305(s14, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 220
    * Starting at 0xf6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4bb

    requires s0.stack[6] == 0x4c0

    requires s0.stack[10] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f72);
      assert s1.Peek(0) == 0xf72;
      assert s1.Peek(4) == 0x4bb;
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
      var s2 := Push2(s1, 0x0f19);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s3, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 216
    * Starting at 0xf19
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xf72

    requires s0.stack[4] == 0x4bb

    requires s0.stack[7] == 0x4c0

    requires s0.stack[11] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf72;
      assert s1.Peek(4) == 0x4bb;
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 307
    * Segment Id for this node is: 222
    * Starting at 0xf73
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4bb

    requires s0.stack[6] == 0x4c0

    requires s0.stack[10] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4bb;
      assert s1.Peek(6) == 0x4c0;
      assert s1.Peek(10) == 0x17f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s6, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 82
    * Starting at 0x4bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4c0;
      assert s1.Peek(7) == 0x17f;
      var s2 := Push2(s1, 0x072b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s3, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 108
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4c0;
      assert s1.Peek(7) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0799);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s319(s10, gas - 1)
      else
        ExecuteFromCFGNode_s310(s10, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 109
    * Starting at 0x75f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4c0;
      assert s1.Peek(8) == 0x17f;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0790);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1077);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s11, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 233
    * Starting at 0x1077
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1077 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x790

    requires s0.stack[5] == 0x4c0

    requires s0.stack[9] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x790;
      assert s1.Peek(5) == 0x4c0;
      assert s1.Peek(9) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x790;
      assert s11.Peek(8) == 0x4c0;
      assert s11.Peek(12) == 0x17f;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x108e);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1055);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s18, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 230
    * Starting at 0x1055
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x108e

    requires s0.stack[4] == 0x790

    requires s0.stack[8] == 0x4c0

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x108e;
      assert s1.Peek(4) == 0x790;
      assert s1.Peek(8) == 0x4c0;
      assert s1.Peek(12) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1061);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s7, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1061

    requires s0.stack[5] == 0x108e

    requires s0.stack[8] == 0x790

    requires s0.stack[12] == 0x4c0

    requires s0.stack[16] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1061;
      assert s1.Peek(5) == 0x108e;
      assert s1.Peek(8) == 0x790;
      assert s1.Peek(12) == 0x4c0;
      assert s1.Peek(16) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1061;
      assert s11.Peek(6) == 0x108e;
      assert s11.Peek(9) == 0x790;
      assert s11.Peek(13) == 0x4c0;
      assert s11.Peek(17) == 0x17f;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s314(s15, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 231
    * Starting at 0x1061
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1061 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x108e

    requires s0.stack[6] == 0x790

    requires s0.stack[10] == 0x4c0

    requires s0.stack[14] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x108e;
      assert s1.Peek(6) == 0x790;
      assert s1.Peek(10) == 0x4c0;
      assert s1.Peek(14) == 0x17f;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1007);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s7, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 229
    * Starting at 0x1007
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1007 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x106c

    requires s0.stack[4] == 0x108e

    requires s0.stack[7] == 0x790

    requires s0.stack[11] == 0x4c0

    requires s0.stack[15] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106c;
      assert s1.Peek(4) == 0x108e;
      assert s1.Peek(7) == 0x790;
      assert s1.Peek(11) == 0x4c0;
      assert s1.Peek(15) == 0x17f;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106c;
      assert s11.Peek(4) == 0x108e;
      assert s11.Peek(7) == 0x790;
      assert s11.Peek(11) == 0x4c0;
      assert s11.Peek(15) == 0x17f;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s13, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 232
    * Starting at 0x106c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x108e

    requires s0.stack[5] == 0x790

    requires s0.stack[9] == 0x4c0

    requires s0.stack[13] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x108e;
      assert s1.Peek(5) == 0x790;
      assert s1.Peek(9) == 0x4c0;
      assert s1.Peek(13) == 0x17f;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s10, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 234
    * Starting at 0x108e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x790

    requires s0.stack[7] == 0x4c0

    requires s0.stack[11] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x790;
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s7, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 110
    * Starting at 0x790
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x790 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4c0

    requires s0.stack[8] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4c0;
      assert s1.Peek(8) == 0x17f;
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

  /** Node 319
    * Segment Id for this node is: 111
    * Starting at 0x799
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4c0;
      assert s1.Peek(7) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0807);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s10, gas - 1)
      else
        ExecuteFromCFGNode_s320(s10, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 112
    * Starting at 0x7cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4c0;
      assert s1.Peek(8) == 0x17f;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07fe);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1105);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s11, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x7fe

    requires s0.stack[5] == 0x4c0

    requires s0.stack[9] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7fe;
      assert s1.Peek(5) == 0x4c0;
      assert s1.Peek(9) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x7fe;
      assert s11.Peek(8) == 0x4c0;
      assert s11.Peek(12) == 0x17f;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x111c);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10e3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s18, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 236
    * Starting at 0x10e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x111c

    requires s0.stack[4] == 0x7fe

    requires s0.stack[8] == 0x4c0

    requires s0.stack[12] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111c;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(8) == 0x4c0;
      assert s1.Peek(12) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10ef);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s7, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x10ef

    requires s0.stack[5] == 0x111c

    requires s0.stack[8] == 0x7fe

    requires s0.stack[12] == 0x4c0

    requires s0.stack[16] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ef;
      assert s1.Peek(5) == 0x111c;
      assert s1.Peek(8) == 0x7fe;
      assert s1.Peek(12) == 0x4c0;
      assert s1.Peek(16) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x10ef;
      assert s11.Peek(6) == 0x111c;
      assert s11.Peek(9) == 0x7fe;
      assert s11.Peek(13) == 0x4c0;
      assert s11.Peek(17) == 0x17f;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s15, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 237
    * Starting at 0x10ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x111c

    requires s0.stack[6] == 0x7fe

    requires s0.stack[10] == 0x4c0

    requires s0.stack[14] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x111c;
      assert s1.Peek(6) == 0x7fe;
      assert s1.Peek(10) == 0x4c0;
      assert s1.Peek(14) == 0x17f;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10fa);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1095);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s7, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 235
    * Starting at 0x1095
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1095 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x10fa

    requires s0.stack[4] == 0x111c

    requires s0.stack[7] == 0x7fe

    requires s0.stack[11] == 0x4c0

    requires s0.stack[15] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10fa;
      assert s1.Peek(4) == 0x111c;
      assert s1.Peek(7) == 0x7fe;
      assert s1.Peek(11) == 0x4c0;
      assert s1.Peek(15) == 0x17f;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10fa;
      assert s11.Peek(4) == 0x111c;
      assert s11.Peek(7) == 0x7fe;
      assert s11.Peek(11) == 0x4c0;
      assert s11.Peek(15) == 0x17f;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s13, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 238
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x111c

    requires s0.stack[5] == 0x7fe

    requires s0.stack[9] == 0x4c0

    requires s0.stack[13] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111c;
      assert s1.Peek(5) == 0x7fe;
      assert s1.Peek(9) == 0x4c0;
      assert s1.Peek(13) == 0x17f;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s10, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 240
    * Starting at 0x111c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x7fe

    requires s0.stack[7] == 0x4c0

    requires s0.stack[11] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7fe;
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s7, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 113
    * Starting at 0x7fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4c0

    requires s0.stack[8] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4c0;
      assert s1.Peek(8) == 0x17f;
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
    * Segment Id for this node is: 114
    * Starting at 0x807
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4c0;
      assert s1.Peek(7) == 0x17f;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x4c0;
      assert s11.Peek(10) == 0x17f;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x4c0;
      assert s21.Peek(10) == 0x17f;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x4c0;
      assert s31.Peek(10) == 0x17f;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s330(s41, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 115
    * Starting at 0x885
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x885 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4c0

    requires s0.stack[7] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x4c0;
      assert s1.Peek(8) == 0x17f;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(9) == 0x4c0;
      assert s11.Peek(13) == 0x17f;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0d28);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s331(s15, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x8e1

    requires s0.stack[9] == 0x4c0

    requires s0.stack[13] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e1;
      assert s1.Peek(9) == 0x4c0;
      assert s1.Peek(13) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x8e1;
      assert s11.Peek(12) == 0x4c0;
      assert s11.Peek(16) == 0x17f;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s14, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x8e1

    requires s0.stack[13] == 0x4c0

    requires s0.stack[17] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x8e1;
      assert s1.Peek(13) == 0x4c0;
      assert s1.Peek(17) == 0x17f;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s5, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x8e1

    requires s0.stack[15] == 0x4c0

    requires s0.stack[19] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x8e1;
      assert s1.Peek(15) == 0x4c0;
      assert s1.Peek(19) == 0x17f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s9, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x8e1

    requires s0.stack[14] == 0x4c0

    requires s0.stack[18] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x8e1;
      assert s1.Peek(14) == 0x4c0;
      assert s1.Peek(18) == 0x17f;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s6, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x8e1

    requires s0.stack[10] == 0x4c0

    requires s0.stack[14] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e1;
      assert s1.Peek(10) == 0x4c0;
      assert s1.Peek(14) == 0x17f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s6, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 116
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x4c0

    requires s0.stack[11] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x4c0;
      assert s1.Peek(11) == 0x17f;
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
      assert s11.Peek(0) == 0x4c0;
      assert s11.Peek(4) == 0x17f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s12, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 83
    * Starting at 0x4c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x17f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x17f;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s338(s9, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 36
    * Starting at 0x17f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x018c);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d00);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s8, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 174
    * Starting at 0xd00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x18c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x18c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d13);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd13;
      assert s11.Peek(5) == 0x18c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0cf1);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s14, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 172
    * Starting at 0xcf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd13

    requires s0.stack[6] == 0x18c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd13;
      assert s1.Peek(6) == 0x18c;
      var s2 := Push2(s1, 0x0cfa);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0ce6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s5, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 171
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcfa

    requires s0.stack[4] == 0xd13

    requires s0.stack[8] == 0x18c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcfa;
      assert s1.Peek(4) == 0xd13;
      assert s1.Peek(8) == 0x18c;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s11, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 173
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd13

    requires s0.stack[7] == 0x18c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd13;
      assert s1.Peek(7) == 0x18c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s343(s6, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 175
    * Starting at 0xd13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x18c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x18c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s6, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 37
    * Starting at 0x18c
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18c as nat
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

  /** Node 345
    * Segment Id for this node is: 11
    * Starting at 0x6f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f as nat
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
      var s5 := Push2(s4, 0x00ab);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s568(s6, gas - 1)
      else
        ExecuteFromCFGNode_s346(s6, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 12
    * Starting at 0x7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00c9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s505(s5, gas - 1)
      else
        ExecuteFromCFGNode_s347(s5, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00f9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s496(s5, gas - 1)
      else
        ExecuteFromCFGNode_s348(s5, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 14
    * Starting at 0x91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0117);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s359(s5, gas - 1)
      else
        ExecuteFromCFGNode_s349(s5, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 15
    * Starting at 0x9c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0147);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s350(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 31
    * Starting at 0x147
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x014f);
      var s3 := Push2(s2, 0x041b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s4, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 78
    * Starting at 0x41b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x14f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x14f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x12);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s7, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 32
    * Starting at 0x14f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x015c);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0dac);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s8, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 190
    * Starting at 0xdac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0dbf);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xdbf;
      assert s11.Peek(5) == 0x15c;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d9d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s14, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 188
    * Starting at 0xd9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xdbf

    requires s0.stack[6] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdbf;
      assert s1.Peek(6) == 0x15c;
      var s2 := Push2(s1, 0x0da6);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0d91);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s5, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 187
    * Starting at 0xd91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xda6

    requires s0.stack[4] == 0xdbf

    requires s0.stack[8] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda6;
      assert s1.Peek(4) == 0xdbf;
      assert s1.Peek(8) == 0x15c;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0xff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s11, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 189
    * Starting at 0xda6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xdbf

    requires s0.stack[7] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdbf;
      assert s1.Peek(7) == 0x15c;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s6, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 191
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x15c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15c;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s6, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 33
    * Starting at 0x15c
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
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

  /** Node 359
    * Segment Id for this node is: 27
    * Starting at 0x117
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0131);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x012c);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x12c;
      assert s11.Peek(3) == 0x131;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0d41);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s14, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 180
    * Starting at 0xd41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x12c

    requires s0.stack[3] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12c;
      assert s1.Peek(3) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0d58);
      assert s11.Peek(0) == 0xd58;
      assert s11.Peek(7) == 0x12c;
      assert s11.Peek(8) == 0x131;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s363(s12, gas - 1)
      else
        ExecuteFromCFGNode_s361(s12, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 181
    * Starting at 0xd50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x12c

    requires s0.stack[6] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0d57);
      assert s1.Peek(0) == 0xd57;
      assert s1.Peek(6) == 0x12c;
      assert s1.Peek(7) == 0x131;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s3, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xd57

    requires s0.stack[6] == 0x12c

    requires s0.stack[7] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xd57;
      assert s1.Peek(6) == 0x12c;
      assert s1.Peek(7) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 363
    * Segment Id for this node is: 183
    * Starting at 0xd58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x12c

    requires s0.stack[6] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x12c;
      assert s1.Peek(6) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0d65);
      var s4 := Dup7(s3);
      var s5 := Dup3(s4);
      var s6 := Dup8(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s9, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd65

    requires s0.stack[9] == 0x12c

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd65;
      assert s1.Peek(9) == 0x12c;
      assert s1.Peek(10) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s10, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xd65

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xd65;
      assert s1.Peek(12) == 0x12c;
      assert s1.Peek(13) == 0x131;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s5, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xd65

    requires s0.stack[14] == 0x12c

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xd65;
      assert s1.Peek(14) == 0x12c;
      assert s1.Peek(15) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s6, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xd65

    requires s0.stack[17] == 0x12c

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xd65;
      assert s1.Peek(17) == 0x12c;
      assert s1.Peek(18) == 0x131;
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
      ExecuteFromCFGNode_s368(s11, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xd65

    requires s0.stack[16] == 0x12c

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xd65;
      assert s1.Peek(16) == 0x12c;
      assert s1.Peek(17) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s7, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xd65

    requires s0.stack[13] == 0x12c

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xd65;
      assert s1.Peek(13) == 0x12c;
      assert s1.Peek(14) == 0x131;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s371(s5, gas - 1)
      else
        ExecuteFromCFGNode_s370(s5, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xd65

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xd65;
      assert s1.Peek(13) == 0x12c;
      assert s1.Peek(14) == 0x131;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 371
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xd65

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xd65;
      assert s1.Peek(12) == 0x12c;
      assert s1.Peek(13) == 0x131;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s3, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd65

    requires s0.stack[10] == 0x12c

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd65;
      assert s1.Peek(10) == 0x12c;
      assert s1.Peek(11) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s6, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 184
    * Starting at 0xd65
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x12c

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x12c;
      assert s1.Peek(8) == 0x131;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0d76);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c61);
      assert s11.Peek(0) == 0xc61;
      assert s11.Peek(3) == 0xd76;
      assert s11.Peek(10) == 0x12c;
      assert s11.Peek(11) == 0x131;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s12, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd76

    requires s0.stack[9] == 0x12c

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd76;
      assert s1.Peek(9) == 0x12c;
      assert s1.Peek(10) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s10, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xd76

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xd76;
      assert s1.Peek(12) == 0x12c;
      assert s1.Peek(13) == 0x131;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s5, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xd76

    requires s0.stack[14] == 0x12c

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xd76;
      assert s1.Peek(14) == 0x12c;
      assert s1.Peek(15) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s6, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xd76

    requires s0.stack[17] == 0x12c

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xd76;
      assert s1.Peek(17) == 0x12c;
      assert s1.Peek(18) == 0x131;
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
      ExecuteFromCFGNode_s378(s11, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xd76

    requires s0.stack[16] == 0x12c

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xd76;
      assert s1.Peek(16) == 0x12c;
      assert s1.Peek(17) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s7, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xd76

    requires s0.stack[13] == 0x12c

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xd76;
      assert s1.Peek(13) == 0x12c;
      assert s1.Peek(14) == 0x131;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s381(s5, gas - 1)
      else
        ExecuteFromCFGNode_s380(s5, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xd76

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xd76;
      assert s1.Peek(13) == 0x12c;
      assert s1.Peek(14) == 0x131;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 381
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xd76

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xd76;
      assert s1.Peek(12) == 0x12c;
      assert s1.Peek(13) == 0x131;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s3, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd76

    requires s0.stack[10] == 0x12c

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd76;
      assert s1.Peek(10) == 0x12c;
      assert s1.Peek(11) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s6, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 185
    * Starting at 0xd76
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd76 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x12c

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x12c;
      assert s1.Peek(8) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Push2(s5, 0x0d87);
      var s7 := Dup7(s6);
      var s8 := Dup3(s7);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c94);
      assert s11.Peek(0) == 0xc94;
      assert s11.Peek(3) == 0xd87;
      assert s11.Peek(10) == 0x12c;
      assert s11.Peek(11) == 0x131;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s12, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 163
    * Starting at 0xc94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd87

    requires s0.stack[9] == 0x12c

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd87;
      assert s1.Peek(9) == 0x12c;
      assert s1.Peek(10) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ca2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c7e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s10, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 159
    * Starting at 0xc7e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xd87

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xd87;
      assert s1.Peek(12) == 0x12c;
      assert s1.Peek(13) == 0x131;
      var s2 := Push2(s1, 0x0c87);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s5, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xc87

    requires s0.stack[3] == 0xca2

    requires s0.stack[7] == 0xd87

    requires s0.stack[14] == 0x12c

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc87;
      assert s1.Peek(3) == 0xca2;
      assert s1.Peek(7) == 0xd87;
      assert s1.Peek(14) == 0x12c;
      assert s1.Peek(15) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s9, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 160
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xca2

    requires s0.stack[6] == 0xd87

    requires s0.stack[13] == 0x12c

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xd87;
      assert s1.Peek(13) == 0x12c;
      assert s1.Peek(14) == 0x131;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c91);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s389(s5, gas - 1)
      else
        ExecuteFromCFGNode_s388(s5, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 161
    * Starting at 0xc8e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xd87

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xd87;
      assert s1.Peek(13) == 0x12c;
      assert s1.Peek(14) == 0x131;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 389
    * Segment Id for this node is: 162
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xd87

    requires s0.stack[12] == 0x12c

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xd87;
      assert s1.Peek(12) == 0x12c;
      assert s1.Peek(13) == 0x131;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s3, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 164
    * Starting at 0xca2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xd87

    requires s0.stack[10] == 0x12c

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd87;
      assert s1.Peek(10) == 0x12c;
      assert s1.Peek(11) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s6, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 186
    * Starting at 0xd87
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x12c

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x12c;
      assert s1.Peek(8) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s392(s10, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 28
    * Starting at 0x12c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x131;
      var s2 := Push2(s1, 0x0329);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s3, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 70
    * Starting at 0x329
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x329 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0335);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x08ee);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s8, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 117
    * Starting at 0x8ee
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x335

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x335;
      assert s1.Peek(8) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x095c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s404(s10, gas - 1)
      else
        ExecuteFromCFGNode_s395(s10, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 118
    * Starting at 0x922
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x922 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x335

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x335;
      assert s1.Peek(9) == 0x131;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0953);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1193);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s11, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 245
    * Starting at 0x1193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x953

    requires s0.stack[5] == 0x335

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x953;
      assert s1.Peek(5) == 0x335;
      assert s1.Peek(10) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x953;
      assert s11.Peek(8) == 0x335;
      assert s11.Peek(13) == 0x131;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x11aa);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1171);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s18, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 242
    * Starting at 0x1171
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x11aa

    requires s0.stack[4] == 0x953

    requires s0.stack[8] == 0x335

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11aa;
      assert s1.Peek(4) == 0x953;
      assert s1.Peek(8) == 0x335;
      assert s1.Peek(13) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x117d);
      var s4 := Push1(s3, 0x25);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s7, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x117d

    requires s0.stack[5] == 0x11aa

    requires s0.stack[8] == 0x953

    requires s0.stack[12] == 0x335

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x117d;
      assert s1.Peek(5) == 0x11aa;
      assert s1.Peek(8) == 0x953;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x117d;
      assert s11.Peek(6) == 0x11aa;
      assert s11.Peek(9) == 0x953;
      assert s11.Peek(13) == 0x335;
      assert s11.Peek(18) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s15, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 243
    * Starting at 0x117d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x11aa

    requires s0.stack[6] == 0x953

    requires s0.stack[10] == 0x335

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11aa;
      assert s1.Peek(6) == 0x953;
      assert s1.Peek(10) == 0x335;
      assert s1.Peek(15) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1188);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1123);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s7, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 241
    * Starting at 0x1123
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1123 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1188

    requires s0.stack[4] == 0x11aa

    requires s0.stack[7] == 0x953

    requires s0.stack[11] == 0x335

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1188;
      assert s1.Peek(4) == 0x11aa;
      assert s1.Peek(7) == 0x953;
      assert s1.Peek(11) == 0x335;
      assert s1.Peek(16) == 0x131;
      var s2 := Push32(s1, 0x45524332303a207472616e736665722066726f6d20746865207a65726f206164);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6472657373000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1188;
      assert s11.Peek(4) == 0x11aa;
      assert s11.Peek(7) == 0x953;
      assert s11.Peek(11) == 0x335;
      assert s11.Peek(16) == 0x131;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s13, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 244
    * Starting at 0x1188
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x11aa

    requires s0.stack[5] == 0x953

    requires s0.stack[9] == 0x335

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11aa;
      assert s1.Peek(5) == 0x953;
      assert s1.Peek(9) == 0x335;
      assert s1.Peek(14) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s10, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 246
    * Starting at 0x11aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x953

    requires s0.stack[7] == 0x335

    requires s0.stack[12] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x953;
      assert s1.Peek(7) == 0x335;
      assert s1.Peek(12) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s7, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 119
    * Starting at 0x953
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x953 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x335

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x335;
      assert s1.Peek(9) == 0x131;
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

  /** Node 404
    * Segment Id for this node is: 120
    * Starting at 0x95c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x335

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x335;
      assert s1.Peek(8) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x09ca);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s414(s10, gas - 1)
      else
        ExecuteFromCFGNode_s405(s10, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 121
    * Starting at 0x990
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x990 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x335

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x335;
      assert s1.Peek(9) == 0x131;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x09c1);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1221);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s11, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 251
    * Starting at 0x1221
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1221 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x9c1

    requires s0.stack[5] == 0x335

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9c1;
      assert s1.Peek(5) == 0x335;
      assert s1.Peek(10) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x9c1;
      assert s11.Peek(8) == 0x335;
      assert s11.Peek(13) == 0x131;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x1238);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x11ff);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s18, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 248
    * Starting at 0x11ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x1238

    requires s0.stack[4] == 0x9c1

    requires s0.stack[8] == 0x335

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1238;
      assert s1.Peek(4) == 0x9c1;
      assert s1.Peek(8) == 0x335;
      assert s1.Peek(13) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x120b);
      var s4 := Push1(s3, 0x23);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s7, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x120b

    requires s0.stack[5] == 0x1238

    requires s0.stack[8] == 0x9c1

    requires s0.stack[12] == 0x335

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x120b;
      assert s1.Peek(5) == 0x1238;
      assert s1.Peek(8) == 0x9c1;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x120b;
      assert s11.Peek(6) == 0x1238;
      assert s11.Peek(9) == 0x9c1;
      assert s11.Peek(13) == 0x335;
      assert s11.Peek(18) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s409(s15, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 249
    * Starting at 0x120b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x1238

    requires s0.stack[6] == 0x9c1

    requires s0.stack[10] == 0x335

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1238;
      assert s1.Peek(6) == 0x9c1;
      assert s1.Peek(10) == 0x335;
      assert s1.Peek(15) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x1216);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x11b1);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s7, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 247
    * Starting at 0x11b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x1216

    requires s0.stack[4] == 0x1238

    requires s0.stack[7] == 0x9c1

    requires s0.stack[11] == 0x335

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1216;
      assert s1.Peek(4) == 0x1238;
      assert s1.Peek(7) == 0x9c1;
      assert s1.Peek(11) == 0x335;
      assert s1.Peek(16) == 0x131;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220746f20746865207a65726f2061646472);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6573730000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x1216;
      assert s11.Peek(4) == 0x1238;
      assert s11.Peek(7) == 0x9c1;
      assert s11.Peek(11) == 0x335;
      assert s11.Peek(16) == 0x131;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s13, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 250
    * Starting at 0x1216
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1216 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1238

    requires s0.stack[5] == 0x9c1

    requires s0.stack[9] == 0x335

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1238;
      assert s1.Peek(5) == 0x9c1;
      assert s1.Peek(9) == 0x335;
      assert s1.Peek(14) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s10, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 252
    * Starting at 0x1238
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1238 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9c1

    requires s0.stack[7] == 0x335

    requires s0.stack[12] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9c1;
      assert s1.Peek(7) == 0x335;
      assert s1.Peek(12) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s7, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 122
    * Starting at 0x9c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x335

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x335;
      assert s1.Peek(9) == 0x131;
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

  /** Node 414
    * Segment Id for this node is: 123
    * Starting at 0x9ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x335

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x335;
      assert s1.Peek(8) == 0x131;
      var s2 := Push2(s1, 0x09d5);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b63);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s7, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 132
    * Starting at 0xb63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x9d5

    requires s0.stack[7] == 0x335

    requires s0.stack[12] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9d5;
      assert s1.Peek(7) == 0x335;
      assert s1.Peek(12) == 0x131;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s5, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 124
    * Starting at 0x9d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x335

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x335;
      assert s1.Peek(8) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x335;
      assert s11.Peek(11) == 0x131;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := SLoad(s20);
      assert s21.Peek(5) == 0x335;
      assert s21.Peek(10) == 0x131;
      var s22 := Swap1(s21);
      var s23 := Pop(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Lt(s25);
      var s27 := IsZero(s26);
      var s28 := Push2(s27, 0x0a58);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s426(s29, gas - 1)
      else
        ExecuteFromCFGNode_s417(s29, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 125
    * Starting at 0xa1e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x335

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x335;
      assert s1.Peek(10) == 0x131;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0a4f);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x12af);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s11, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 257
    * Starting at 0x12af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xa4f

    requires s0.stack[6] == 0x335

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa4f;
      assert s1.Peek(6) == 0x335;
      assert s1.Peek(11) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0xa4f;
      assert s11.Peek(9) == 0x335;
      assert s11.Peek(14) == 0x131;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x12c6);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x128d);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s419(s18, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 254
    * Starting at 0x128d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x12c6

    requires s0.stack[4] == 0xa4f

    requires s0.stack[9] == 0x335

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12c6;
      assert s1.Peek(4) == 0xa4f;
      assert s1.Peek(9) == 0x335;
      assert s1.Peek(14) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1299);
      var s4 := Push1(s3, 0x26);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s7, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1299

    requires s0.stack[5] == 0x12c6

    requires s0.stack[8] == 0xa4f

    requires s0.stack[13] == 0x335

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1299;
      assert s1.Peek(5) == 0x12c6;
      assert s1.Peek(8) == 0xa4f;
      assert s1.Peek(13) == 0x335;
      assert s1.Peek(18) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1299;
      assert s11.Peek(6) == 0x12c6;
      assert s11.Peek(9) == 0xa4f;
      assert s11.Peek(14) == 0x335;
      assert s11.Peek(19) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s15, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 255
    * Starting at 0x1299
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x12c6

    requires s0.stack[6] == 0xa4f

    requires s0.stack[11] == 0x335

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12c6;
      assert s1.Peek(6) == 0xa4f;
      assert s1.Peek(11) == 0x335;
      assert s1.Peek(16) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x12a4);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x123f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s7, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 253
    * Starting at 0x123f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x12a4

    requires s0.stack[4] == 0x12c6

    requires s0.stack[7] == 0xa4f

    requires s0.stack[12] == 0x335

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x12a4;
      assert s1.Peek(4) == 0x12c6;
      assert s1.Peek(7) == 0xa4f;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732062);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x616c616e63650000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x12a4;
      assert s11.Peek(4) == 0x12c6;
      assert s11.Peek(7) == 0xa4f;
      assert s11.Peek(12) == 0x335;
      assert s11.Peek(17) == 0x131;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s13, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 256
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x12c6

    requires s0.stack[5] == 0xa4f

    requires s0.stack[10] == 0x335

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12c6;
      assert s1.Peek(5) == 0xa4f;
      assert s1.Peek(10) == 0x335;
      assert s1.Peek(15) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s10, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 258
    * Starting at 0x12c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa4f

    requires s0.stack[8] == 0x335

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa4f;
      assert s1.Peek(8) == 0x335;
      assert s1.Peek(13) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s7, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 126
    * Starting at 0xa4f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x335

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x335;
      assert s1.Peek(10) == 0x131;
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

  /** Node 426
    * Segment Id for this node is: 127
    * Starting at 0xa58
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x335

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x335;
      assert s1.Peek(9) == 0x131;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Push0(s4);
      var s6 := Dup1(s5);
      var s7 := Dup7(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x335;
      assert s11.Peek(13) == 0x131;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x335;
      assert s21.Peek(12) == 0x131;
      var s22 := Keccak256(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Dup2(s26);
      var s28 := Push0(s27);
      var s29 := Dup1(s28);
      var s30 := Dup6(s29);
      var s31 := Push20(s30, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s31.Peek(9) == 0x335;
      assert s31.Peek(14) == 0x131;
      var s32 := And(s31);
      var s33 := Push20(s32, 0xffffffffffffffffffffffffffffffffffffffff);
      var s34 := And(s33);
      var s35 := Dup2(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Add(s37);
      var s39 := Swap1(s38);
      var s40 := Dup2(s39);
      var s41 := MStore(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s427(s41, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 128
    * Starting at 0xad4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x335

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x335;
      assert s1.Peek(12) == 0x131;
      var s2 := Add(s1);
      var s3 := Push0(s2);
      var s4 := Keccak256(s3);
      var s5 := Push0(s4);
      var s6 := Dup3(s5);
      var s7 := Dup3(s6);
      var s8 := SLoad(s7);
      var s9 := Push2(s8, 0x0ae6);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xae6;
      assert s11.Peek(10) == 0x335;
      assert s11.Peek(15) == 0x131;
      var s12 := Push2(s11, 0x0f46);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s13, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 217
    * Starting at 0xf46
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xae6

    requires s0.stack[10] == 0x335

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xae6;
      assert s1.Peek(10) == 0x335;
      assert s1.Peek(15) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0f50);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c75);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s429(s6, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xf50

    requires s0.stack[5] == 0xae6

    requires s0.stack[13] == 0x335

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf50;
      assert s1.Peek(5) == 0xae6;
      assert s1.Peek(13) == 0x335;
      assert s1.Peek(18) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s9, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 218
    * Starting at 0xf50
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xae6

    requires s0.stack[12] == 0x335

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0f5b);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0c75);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s7, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xf5b

    requires s0.stack[5] == 0xae6

    requires s0.stack[13] == 0x335

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf5b;
      assert s1.Peek(5) == 0xae6;
      assert s1.Peek(13) == 0x335;
      assert s1.Peek(18) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s9, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 219
    * Starting at 0xf5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xae6

    requires s0.stack[12] == 0x335

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(4) == 0xae6;
      assert s11.Peek(12) == 0x335;
      assert s11.Peek(17) == 0x131;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0f73);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s435(s14, gas - 1)
      else
        ExecuteFromCFGNode_s433(s14, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 220
    * Starting at 0xf6b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xae6

    requires s0.stack[11] == 0x335

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f72);
      assert s1.Peek(0) == 0xf72;
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Push2(s1, 0x0f19);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s3, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 216
    * Starting at 0xf19
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0xf72

    requires s0.stack[4] == 0xae6

    requires s0.stack[12] == 0x335

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf72;
      assert s1.Peek(4) == 0xae6;
      assert s1.Peek(12) == 0x335;
      assert s1.Peek(17) == 0x131;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 435
    * Segment Id for this node is: 222
    * Starting at 0xf73
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xae6

    requires s0.stack[11] == 0x335

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xae6;
      assert s1.Peek(11) == 0x335;
      assert s1.Peek(16) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s6, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 129
    * Starting at 0xae6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x335

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x335;
      assert s1.Peek(13) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Dup2(s4);
      var s6 := Swap1(s5);
      var s7 := SStore(s6);
      var s8 := Pop(s7);
      var s9 := Dup3(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(5) == 0x335;
      assert s11.Peek(10) == 0x131;
      var s12 := Dup5(s11);
      var s13 := Push20(s12, 0xffffffffffffffffffffffffffffffffffffffff);
      var s14 := And(s13);
      var s15 := Push32(s14, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s16 := Dup5(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := MLoad(s17);
      var s19 := Push2(s18, 0x0b4a);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0xb4a;
      assert s21.Peek(10) == 0x335;
      assert s21.Peek(15) == 0x131;
      var s22 := Push2(s21, 0x0d28);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s437(s23, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xb4a

    requires s0.stack[10] == 0x335

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb4a;
      assert s1.Peek(10) == 0x335;
      assert s1.Peek(15) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0xb4a;
      assert s11.Peek(13) == 0x335;
      assert s11.Peek(18) == 0x131;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s438(s14, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0xb4a

    requires s0.stack[14] == 0x335

    requires s0.stack[19] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0xb4a;
      assert s1.Peek(14) == 0x335;
      assert s1.Peek(19) == 0x131;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s5, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0xb4a

    requires s0.stack[16] == 0x335

    requires s0.stack[21] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0xb4a;
      assert s1.Peek(16) == 0x335;
      assert s1.Peek(21) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s9, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0xb4a

    requires s0.stack[15] == 0x335

    requires s0.stack[20] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0xb4a;
      assert s1.Peek(15) == 0x335;
      assert s1.Peek(20) == 0x131;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s441(s6, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xb4a

    requires s0.stack[11] == 0x335

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb4a;
      assert s1.Peek(11) == 0x335;
      assert s1.Peek(16) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s6, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 130
    * Starting at 0xb4a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x335

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x335;
      assert s1.Peek(13) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log3(s7);
      var s9 := Push2(s8, 0x0b5d);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(2) == 0xb5d;
      assert s11.Peek(7) == 0x335;
      assert s11.Peek(12) == 0x131;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0b68);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s14, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 133
    * Starting at 0xb68
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xb5d

    requires s0.stack[8] == 0x335

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb5d;
      assert s1.Peek(8) == 0x335;
      assert s1.Peek(13) == 0x131;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s5, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 131
    * Starting at 0xb5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x335

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x335;
      assert s1.Peek(9) == 0x131;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s445(s6, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 71
    * Starting at 0x335
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup7(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x131;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(7) == 0x131;
      var s22 := Push2(s21, 0x037c);
      var s23 := Push2(s22, 0x0724);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s24, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x37c

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x37c;
      assert s1.Peek(8) == 0x131;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s7, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 72
    * Starting at 0x37c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x131;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x131;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push0(s14);
      var s16 := Keccak256(s15);
      var s17 := SLoad(s16);
      var s18 := Swap1(s17);
      var s19 := Pop(s18);
      var s20 := Dup3(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x131;
      var s22 := Lt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x03fb);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s457(s25, gas - 1)
      else
        ExecuteFromCFGNode_s448(s25, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 73
    * Starting at 0x3c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x131;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x03f2);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0efb);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s449(s11, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 214
    * Starting at 0xefb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3f2

    requires s0.stack[7] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3f2;
      assert s1.Peek(7) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x3f2;
      assert s11.Peek(10) == 0x131;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0f12);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x0ed9);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s18, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 211
    * Starting at 0xed9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xf12

    requires s0.stack[4] == 0x3f2

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf12;
      assert s1.Peek(4) == 0x3f2;
      assert s1.Peek(10) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ee5);
      var s4 := Push1(s3, 0x28);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s7, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xee5

    requires s0.stack[5] == 0xf12

    requires s0.stack[8] == 0x3f2

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xee5;
      assert s1.Peek(5) == 0xf12;
      assert s1.Peek(8) == 0x3f2;
      assert s1.Peek(14) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xee5;
      assert s11.Peek(6) == 0xf12;
      assert s11.Peek(9) == 0x3f2;
      assert s11.Peek(15) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s15, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 212
    * Starting at 0xee5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xf12

    requires s0.stack[6] == 0x3f2

    requires s0.stack[12] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf12;
      assert s1.Peek(6) == 0x3f2;
      assert s1.Peek(12) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0ef0);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x0e8b);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s7, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 210
    * Starting at 0xe8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xef0

    requires s0.stack[4] == 0xf12

    requires s0.stack[7] == 0x3f2

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xef0;
      assert s1.Peek(4) == 0xf12;
      assert s1.Peek(7) == 0x3f2;
      assert s1.Peek(13) == 0x131;
      var s2 := Push32(s1, 0x45524332303a207472616e7366657220616d6f756e7420657863656564732061);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x6c6c6f77616e6365000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xef0;
      assert s11.Peek(4) == 0xf12;
      assert s11.Peek(7) == 0x3f2;
      assert s11.Peek(13) == 0x131;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s13, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 213
    * Starting at 0xef0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xf12

    requires s0.stack[5] == 0x3f2

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf12;
      assert s1.Peek(5) == 0x3f2;
      assert s1.Peek(11) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s10, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 215
    * Starting at 0xf12
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3f2

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3f2;
      assert s1.Peek(9) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s7, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 74
    * Starting at 0x3f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x131;
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

  /** Node 457
    * Segment Id for this node is: 75
    * Starting at 0x3fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x131;
      var s2 := Push2(s1, 0x040f);
      var s3 := Dup6(s2);
      var s4 := Push2(s3, 0x0407);
      var s5 := Push2(s4, 0x0724);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s6, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x407

    requires s0.stack[2] == 0x40f

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x407;
      assert s1.Peek(2) == 0x40f;
      assert s1.Peek(8) == 0x131;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s7, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 76
    * Starting at 0x407
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x407 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x40f

    requires s0.stack[8] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x40f;
      assert s1.Peek(8) == 0x131;
      var s2 := Dup6(s1);
      var s3 := Dup5(s2);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x072b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s6, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 108
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x40f

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x40f;
      assert s1.Peek(9) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0799);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s470(s10, gas - 1)
      else
        ExecuteFromCFGNode_s461(s10, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 109
    * Starting at 0x75f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x40f

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x40f;
      assert s1.Peek(10) == 0x131;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0790);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1077);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s11, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 233
    * Starting at 0x1077
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1077 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x790

    requires s0.stack[5] == 0x40f

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x790;
      assert s1.Peek(5) == 0x40f;
      assert s1.Peek(11) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x790;
      assert s11.Peek(8) == 0x40f;
      assert s11.Peek(14) == 0x131;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x108e);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1055);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s18, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 230
    * Starting at 0x1055
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x108e

    requires s0.stack[4] == 0x790

    requires s0.stack[8] == 0x40f

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x108e;
      assert s1.Peek(4) == 0x790;
      assert s1.Peek(8) == 0x40f;
      assert s1.Peek(14) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1061);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s7, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x1061

    requires s0.stack[5] == 0x108e

    requires s0.stack[8] == 0x790

    requires s0.stack[12] == 0x40f

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1061;
      assert s1.Peek(5) == 0x108e;
      assert s1.Peek(8) == 0x790;
      assert s1.Peek(12) == 0x40f;
      assert s1.Peek(18) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1061;
      assert s11.Peek(6) == 0x108e;
      assert s11.Peek(9) == 0x790;
      assert s11.Peek(13) == 0x40f;
      assert s11.Peek(19) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s465(s15, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 231
    * Starting at 0x1061
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1061 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x108e

    requires s0.stack[6] == 0x790

    requires s0.stack[10] == 0x40f

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x108e;
      assert s1.Peek(6) == 0x790;
      assert s1.Peek(10) == 0x40f;
      assert s1.Peek(16) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1007);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s7, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 229
    * Starting at 0x1007
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1007 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x106c

    requires s0.stack[4] == 0x108e

    requires s0.stack[7] == 0x790

    requires s0.stack[11] == 0x40f

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106c;
      assert s1.Peek(4) == 0x108e;
      assert s1.Peek(7) == 0x790;
      assert s1.Peek(11) == 0x40f;
      assert s1.Peek(17) == 0x131;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106c;
      assert s11.Peek(4) == 0x108e;
      assert s11.Peek(7) == 0x790;
      assert s11.Peek(11) == 0x40f;
      assert s11.Peek(17) == 0x131;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s13, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 232
    * Starting at 0x106c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x108e

    requires s0.stack[5] == 0x790

    requires s0.stack[9] == 0x40f

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x108e;
      assert s1.Peek(5) == 0x790;
      assert s1.Peek(9) == 0x40f;
      assert s1.Peek(15) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s10, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 234
    * Starting at 0x108e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x790

    requires s0.stack[7] == 0x40f

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x790;
      assert s1.Peek(7) == 0x40f;
      assert s1.Peek(13) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s7, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 110
    * Starting at 0x790
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x790 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x40f

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x40f;
      assert s1.Peek(10) == 0x131;
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

  /** Node 470
    * Segment Id for this node is: 111
    * Starting at 0x799
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x40f

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x40f;
      assert s1.Peek(9) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0807);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s480(s10, gas - 1)
      else
        ExecuteFromCFGNode_s471(s10, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 112
    * Starting at 0x7cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x40f

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x40f;
      assert s1.Peek(10) == 0x131;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07fe);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1105);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s11, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x7fe

    requires s0.stack[5] == 0x40f

    requires s0.stack[11] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7fe;
      assert s1.Peek(5) == 0x40f;
      assert s1.Peek(11) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x7fe;
      assert s11.Peek(8) == 0x40f;
      assert s11.Peek(14) == 0x131;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x111c);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10e3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s18, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 236
    * Starting at 0x10e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x111c

    requires s0.stack[4] == 0x7fe

    requires s0.stack[8] == 0x40f

    requires s0.stack[14] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111c;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(8) == 0x40f;
      assert s1.Peek(14) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10ef);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s474(s7, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x10ef

    requires s0.stack[5] == 0x111c

    requires s0.stack[8] == 0x7fe

    requires s0.stack[12] == 0x40f

    requires s0.stack[18] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ef;
      assert s1.Peek(5) == 0x111c;
      assert s1.Peek(8) == 0x7fe;
      assert s1.Peek(12) == 0x40f;
      assert s1.Peek(18) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x10ef;
      assert s11.Peek(6) == 0x111c;
      assert s11.Peek(9) == 0x7fe;
      assert s11.Peek(13) == 0x40f;
      assert s11.Peek(19) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s15, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 237
    * Starting at 0x10ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x111c

    requires s0.stack[6] == 0x7fe

    requires s0.stack[10] == 0x40f

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x111c;
      assert s1.Peek(6) == 0x7fe;
      assert s1.Peek(10) == 0x40f;
      assert s1.Peek(16) == 0x131;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10fa);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1095);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s7, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 235
    * Starting at 0x1095
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1095 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x10fa

    requires s0.stack[4] == 0x111c

    requires s0.stack[7] == 0x7fe

    requires s0.stack[11] == 0x40f

    requires s0.stack[17] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10fa;
      assert s1.Peek(4) == 0x111c;
      assert s1.Peek(7) == 0x7fe;
      assert s1.Peek(11) == 0x40f;
      assert s1.Peek(17) == 0x131;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10fa;
      assert s11.Peek(4) == 0x111c;
      assert s11.Peek(7) == 0x7fe;
      assert s11.Peek(11) == 0x40f;
      assert s11.Peek(17) == 0x131;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s13, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 238
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x111c

    requires s0.stack[5] == 0x7fe

    requires s0.stack[9] == 0x40f

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111c;
      assert s1.Peek(5) == 0x7fe;
      assert s1.Peek(9) == 0x40f;
      assert s1.Peek(15) == 0x131;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s478(s10, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 240
    * Starting at 0x111c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x7fe

    requires s0.stack[7] == 0x40f

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7fe;
      assert s1.Peek(7) == 0x40f;
      assert s1.Peek(13) == 0x131;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s7, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 113
    * Starting at 0x7fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x40f

    requires s0.stack[10] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x40f;
      assert s1.Peek(10) == 0x131;
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

  /** Node 480
    * Segment Id for this node is: 114
    * Starting at 0x807
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x40f

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x40f;
      assert s1.Peek(9) == 0x131;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x40f;
      assert s11.Peek(12) == 0x131;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x40f;
      assert s21.Peek(12) == 0x131;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x40f;
      assert s31.Peek(12) == 0x131;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s481(s41, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 115
    * Starting at 0x885
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x885 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x40f

    requires s0.stack[9] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x40f;
      assert s1.Peek(10) == 0x131;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(9) == 0x40f;
      assert s11.Peek(15) == 0x131;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0d28);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s15, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x8e1

    requires s0.stack[9] == 0x40f

    requires s0.stack[15] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e1;
      assert s1.Peek(9) == 0x40f;
      assert s1.Peek(15) == 0x131;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x8e1;
      assert s11.Peek(12) == 0x40f;
      assert s11.Peek(18) == 0x131;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s14, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x8e1

    requires s0.stack[13] == 0x40f

    requires s0.stack[19] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x8e1;
      assert s1.Peek(13) == 0x40f;
      assert s1.Peek(19) == 0x131;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s484(s5, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x8e1

    requires s0.stack[15] == 0x40f

    requires s0.stack[21] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x8e1;
      assert s1.Peek(15) == 0x40f;
      assert s1.Peek(21) == 0x131;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s9, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x8e1

    requires s0.stack[14] == 0x40f

    requires s0.stack[20] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x8e1;
      assert s1.Peek(14) == 0x40f;
      assert s1.Peek(20) == 0x131;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s486(s6, gas - 1)
  }

  /** Node 486
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x8e1

    requires s0.stack[10] == 0x40f

    requires s0.stack[16] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e1;
      assert s1.Peek(10) == 0x40f;
      assert s1.Peek(16) == 0x131;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s6, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 116
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x40f

    requires s0.stack[13] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x40f;
      assert s1.Peek(13) == 0x131;
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
      assert s11.Peek(0) == 0x40f;
      assert s11.Peek(6) == 0x131;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s488(s12, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 77
    * Starting at 0x40f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x131

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x131;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap4(s5);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s489(s11, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 29
    * Starting at 0x131
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x131 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x013e);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d00);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s490(s8, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 174
    * Starting at 0xd00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d13);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd13;
      assert s11.Peek(5) == 0x13e;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0cf1);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s14, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 172
    * Starting at 0xcf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd13

    requires s0.stack[6] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd13;
      assert s1.Peek(6) == 0x13e;
      var s2 := Push2(s1, 0x0cfa);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0ce6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s5, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 171
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcfa

    requires s0.stack[4] == 0xd13

    requires s0.stack[8] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcfa;
      assert s1.Peek(4) == 0xd13;
      assert s1.Peek(8) == 0x13e;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s493(s11, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 173
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd13

    requires s0.stack[7] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd13;
      assert s1.Peek(7) == 0x13e;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s494(s6, gas - 1)
  }

  /** Node 494
    * Segment Id for this node is: 175
    * Starting at 0xd13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x13e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x13e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s6, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 30
    * Starting at 0x13e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e as nat
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

  /** Node 496
    * Segment Id for this node is: 24
    * Starting at 0xf9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0101);
      var s3 := Push2(s2, 0x0320);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s4, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 69
    * Starting at 0x320
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x320 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x101

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x101;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s8, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 25
    * Starting at 0x101
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x010e);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d28);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s8, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x10e;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s14, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x10e;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s5, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x10e;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s9, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x10e;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s503(s6, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x10e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10e;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s6, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 26
    * Starting at 0x10e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e as nat
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

  /** Node 505
    * Segment Id for this node is: 20
    * Starting at 0xc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e3);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x00de);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0xde;
      assert s11.Peek(3) == 0xe3;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0ca8);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s14, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 165
    * Starting at 0xca8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xde

    requires s0.stack[3] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde;
      assert s1.Peek(3) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cbe);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s509(s11, gas - 1)
      else
        ExecuteFromCFGNode_s507(s11, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 166
    * Starting at 0xcb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xde

    requires s0.stack[5] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0cbd);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0xde;
      assert s1.Peek(6) == 0xe3;
      var s2 := Push2(s1, 0x0c17);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s508(s3, gas - 1)
  }

  /** Node 508
    * Segment Id for this node is: 148
    * Starting at 0xc17
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xcbd

    requires s0.stack[5] == 0xde

    requires s0.stack[6] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcbd;
      assert s1.Peek(5) == 0xde;
      assert s1.Peek(6) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 509
    * Segment Id for this node is: 168
    * Starting at 0xcbe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xde

    requires s0.stack[5] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xde;
      assert s1.Peek(5) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0ccb);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0c61);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s510(s9, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 156
    * Starting at 0xc61
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xccb

    requires s0.stack[8] == 0xde

    requires s0.stack[9] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xccb;
      assert s1.Peek(8) == 0xde;
      assert s1.Peek(9) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0c6f);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c4b);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s511(s10, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 152
    * Starting at 0xc4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0xde

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0xde;
      assert s1.Peek(12) == 0xe3;
      var s2 := Push2(s1, 0x0c54);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c3a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s5, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 150
    * Starting at 0xc3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc54

    requires s0.stack[3] == 0xc6f

    requires s0.stack[7] == 0xccb

    requires s0.stack[13] == 0xde

    requires s0.stack[14] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc54;
      assert s1.Peek(3) == 0xc6f;
      assert s1.Peek(7) == 0xccb;
      assert s1.Peek(13) == 0xde;
      assert s1.Peek(14) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0c44);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0c1b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s513(s6, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 149
    * Starting at 0xc1b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xc44

    requires s0.stack[4] == 0xc54

    requires s0.stack[6] == 0xc6f

    requires s0.stack[10] == 0xccb

    requires s0.stack[16] == 0xde

    requires s0.stack[17] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc44;
      assert s1.Peek(4) == 0xc54;
      assert s1.Peek(6) == 0xc6f;
      assert s1.Peek(10) == 0xccb;
      assert s1.Peek(16) == 0xde;
      assert s1.Peek(17) == 0xe3;
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
      ExecuteFromCFGNode_s514(s11, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 151
    * Starting at 0xc44
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc44 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xc54

    requires s0.stack[5] == 0xc6f

    requires s0.stack[9] == 0xccb

    requires s0.stack[15] == 0xde

    requires s0.stack[16] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc54;
      assert s1.Peek(5) == 0xc6f;
      assert s1.Peek(9) == 0xccb;
      assert s1.Peek(15) == 0xde;
      assert s1.Peek(16) == 0xe3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s7, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 153
    * Starting at 0xc54
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xc6f

    requires s0.stack[6] == 0xccb

    requires s0.stack[12] == 0xde

    requires s0.stack[13] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0xde;
      assert s1.Peek(13) == 0xe3;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c5e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s517(s5, gas - 1)
      else
        ExecuteFromCFGNode_s516(s5, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 154
    * Starting at 0xc5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0xde

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xc6f;
      assert s1.Peek(6) == 0xccb;
      assert s1.Peek(12) == 0xde;
      assert s1.Peek(13) == 0xe3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 517
    * Segment Id for this node is: 155
    * Starting at 0xc5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xc6f

    requires s0.stack[5] == 0xccb

    requires s0.stack[11] == 0xde

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc6f;
      assert s1.Peek(5) == 0xccb;
      assert s1.Peek(11) == 0xde;
      assert s1.Peek(12) == 0xe3;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s518(s3, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 157
    * Starting at 0xc6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xccb

    requires s0.stack[9] == 0xde

    requires s0.stack[10] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xccb;
      assert s1.Peek(9) == 0xde;
      assert s1.Peek(10) == 0xe3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s6, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 169
    * Starting at 0xccb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xde

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xde;
      assert s1.Peek(7) == 0xe3;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x0cdc);
      var s7 := Dup6(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0c94);
      assert s11.Peek(0) == 0xc94;
      assert s11.Peek(3) == 0xcdc;
      assert s11.Peek(9) == 0xde;
      assert s11.Peek(10) == 0xe3;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s520(s12, gas - 1)
  }

  /** Node 520
    * Segment Id for this node is: 163
    * Starting at 0xc94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xcdc

    requires s0.stack[8] == 0xde

    requires s0.stack[9] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcdc;
      assert s1.Peek(8) == 0xde;
      assert s1.Peek(9) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0ca2);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c7e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s521(s10, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 159
    * Starting at 0xc7e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0xde

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0xde;
      assert s1.Peek(12) == 0xe3;
      var s2 := Push2(s1, 0x0c87);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s522(s5, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xc87

    requires s0.stack[3] == 0xca2

    requires s0.stack[7] == 0xcdc

    requires s0.stack[13] == 0xde

    requires s0.stack[14] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc87;
      assert s1.Peek(3) == 0xca2;
      assert s1.Peek(7) == 0xcdc;
      assert s1.Peek(13) == 0xde;
      assert s1.Peek(14) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s523(s9, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 160
    * Starting at 0xc87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xca2

    requires s0.stack[6] == 0xcdc

    requires s0.stack[12] == 0xde

    requires s0.stack[13] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0xde;
      assert s1.Peek(13) == 0xe3;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0c91);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s525(s5, gas - 1)
      else
        ExecuteFromCFGNode_s524(s5, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 161
    * Starting at 0xc8e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0xde

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xca2;
      assert s1.Peek(6) == 0xcdc;
      assert s1.Peek(12) == 0xde;
      assert s1.Peek(13) == 0xe3;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 525
    * Segment Id for this node is: 162
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xca2

    requires s0.stack[5] == 0xcdc

    requires s0.stack[11] == 0xde

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xca2;
      assert s1.Peek(5) == 0xcdc;
      assert s1.Peek(11) == 0xde;
      assert s1.Peek(12) == 0xe3;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s3, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 164
    * Starting at 0xca2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0xcdc

    requires s0.stack[9] == 0xde

    requires s0.stack[10] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcdc;
      assert s1.Peek(9) == 0xde;
      assert s1.Peek(10) == 0xe3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s527(s6, gas - 1)
  }

  /** Node 527
    * Segment Id for this node is: 170
    * Starting at 0xcdc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0xde

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xde;
      assert s1.Peek(7) == 0xe3;
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
      ExecuteFromCFGNode_s528(s10, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 21
    * Starting at 0xde
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe3;
      var s2 := Push2(s1, 0x0303);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s529(s3, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 66
    * Starting at 0x303
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x303 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0316);
      var s4 := Push2(s3, 0x030f);
      var s5 := Push2(s4, 0x0724);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s6, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 107
    * Starting at 0x724
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x724 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x30f

    requires s0.stack[1] == 0x316

    requires s0.stack[5] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x30f;
      assert s1.Peek(1) == 0x316;
      assert s1.Peek(5) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Caller(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s531(s7, gas - 1)
  }

  /** Node 531
    * Segment Id for this node is: 67
    * Starting at 0x30f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x316

    requires s0.stack[5] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x316;
      assert s1.Peek(5) == 0xe3;
      var s2 := Dup5(s1);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x072b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s532(s5, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 108
    * Starting at 0x72b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x316

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x316;
      assert s1.Peek(7) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup4(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0799);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s542(s10, gas - 1)
      else
        ExecuteFromCFGNode_s533(s10, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 109
    * Starting at 0x75f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x316

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x316;
      assert s1.Peek(8) == 0xe3;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0790);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1077);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s534(s11, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 233
    * Starting at 0x1077
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1077 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x790

    requires s0.stack[5] == 0x316

    requires s0.stack[9] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x790;
      assert s1.Peek(5) == 0x316;
      assert s1.Peek(9) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x790;
      assert s11.Peek(8) == 0x316;
      assert s11.Peek(12) == 0xe3;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x108e);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x1055);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s535(s18, gas - 1)
  }

  /** Node 535
    * Segment Id for this node is: 230
    * Starting at 0x1055
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x108e

    requires s0.stack[4] == 0x790

    requires s0.stack[8] == 0x316

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x108e;
      assert s1.Peek(4) == 0x790;
      assert s1.Peek(8) == 0x316;
      assert s1.Peek(12) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x1061);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s7, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x1061

    requires s0.stack[5] == 0x108e

    requires s0.stack[8] == 0x790

    requires s0.stack[12] == 0x316

    requires s0.stack[16] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1061;
      assert s1.Peek(5) == 0x108e;
      assert s1.Peek(8) == 0x790;
      assert s1.Peek(12) == 0x316;
      assert s1.Peek(16) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x1061;
      assert s11.Peek(6) == 0x108e;
      assert s11.Peek(9) == 0x790;
      assert s11.Peek(13) == 0x316;
      assert s11.Peek(17) == 0xe3;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s537(s15, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 231
    * Starting at 0x1061
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1061 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x108e

    requires s0.stack[6] == 0x790

    requires s0.stack[10] == 0x316

    requires s0.stack[14] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x108e;
      assert s1.Peek(6) == 0x790;
      assert s1.Peek(10) == 0x316;
      assert s1.Peek(14) == 0xe3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x106c);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1007);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s538(s7, gas - 1)
  }

  /** Node 538
    * Segment Id for this node is: 229
    * Starting at 0x1007
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1007 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x106c

    requires s0.stack[4] == 0x108e

    requires s0.stack[7] == 0x790

    requires s0.stack[11] == 0x316

    requires s0.stack[15] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106c;
      assert s1.Peek(4) == 0x108e;
      assert s1.Peek(7) == 0x790;
      assert s1.Peek(11) == 0x316;
      assert s1.Peek(15) == 0xe3;
      var s2 := Push32(s1, 0x45524332303a20617070726f76652066726f6d20746865207a65726f20616464);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7265737300000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x106c;
      assert s11.Peek(4) == 0x108e;
      assert s11.Peek(7) == 0x790;
      assert s11.Peek(11) == 0x316;
      assert s11.Peek(15) == 0xe3;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s13, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 232
    * Starting at 0x106c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x108e

    requires s0.stack[5] == 0x790

    requires s0.stack[9] == 0x316

    requires s0.stack[13] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x108e;
      assert s1.Peek(5) == 0x790;
      assert s1.Peek(9) == 0x316;
      assert s1.Peek(13) == 0xe3;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s540(s10, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 234
    * Starting at 0x108e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x790

    requires s0.stack[7] == 0x316

    requires s0.stack[11] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x790;
      assert s1.Peek(7) == 0x316;
      assert s1.Peek(11) == 0xe3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s541(s7, gas - 1)
  }

  /** Node 541
    * Segment Id for this node is: 110
    * Starting at 0x790
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x790 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x316

    requires s0.stack[8] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x316;
      assert s1.Peek(8) == 0xe3;
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

  /** Node 542
    * Segment Id for this node is: 111
    * Starting at 0x799
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x316

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x316;
      assert s1.Peek(7) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Dup3(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0807);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s552(s10, gas - 1)
      else
        ExecuteFromCFGNode_s543(s10, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 112
    * Starting at 0x7cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x316

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x316;
      assert s1.Peek(8) == 0xe3;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x07fe);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x1105);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s11, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 239
    * Starting at 0x1105
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x7fe

    requires s0.stack[5] == 0x316

    requires s0.stack[9] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7fe;
      assert s1.Peek(5) == 0x316;
      assert s1.Peek(9) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(4) == 0x7fe;
      assert s11.Peek(8) == 0x316;
      assert s11.Peek(12) == 0xe3;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x111c);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x10e3);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s18, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 236
    * Starting at 0x10e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x111c

    requires s0.stack[4] == 0x7fe

    requires s0.stack[8] == 0x316

    requires s0.stack[12] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x111c;
      assert s1.Peek(4) == 0x7fe;
      assert s1.Peek(8) == 0x316;
      assert s1.Peek(12) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x10ef);
      var s4 := Push1(s3, 0x22);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0b77);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s546(s7, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x10ef

    requires s0.stack[5] == 0x111c

    requires s0.stack[8] == 0x7fe

    requires s0.stack[12] == 0x316

    requires s0.stack[16] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10ef;
      assert s1.Peek(5) == 0x111c;
      assert s1.Peek(8) == 0x7fe;
      assert s1.Peek(12) == 0x316;
      assert s1.Peek(16) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x10ef;
      assert s11.Peek(6) == 0x111c;
      assert s11.Peek(9) == 0x7fe;
      assert s11.Peek(13) == 0x316;
      assert s11.Peek(17) == 0xe3;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s547(s15, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 237
    * Starting at 0x10ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x111c

    requires s0.stack[6] == 0x7fe

    requires s0.stack[10] == 0x316

    requires s0.stack[14] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x111c;
      assert s1.Peek(6) == 0x7fe;
      assert s1.Peek(10) == 0x316;
      assert s1.Peek(14) == 0xe3;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x10fa);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x1095);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s548(s7, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 235
    * Starting at 0x1095
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1095 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x10fa

    requires s0.stack[4] == 0x111c

    requires s0.stack[7] == 0x7fe

    requires s0.stack[11] == 0x316

    requires s0.stack[15] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10fa;
      assert s1.Peek(4) == 0x111c;
      assert s1.Peek(7) == 0x7fe;
      assert s1.Peek(11) == 0x316;
      assert s1.Peek(15) == 0xe3;
      var s2 := Push32(s1, 0x45524332303a20617070726f766520746f20746865207a65726f206164647265);
      var s3 := Push0(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Push32(s6, 0x7373000000000000000000000000000000000000000000000000000000000000);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x10fa;
      assert s11.Peek(4) == 0x111c;
      assert s11.Peek(7) == 0x7fe;
      assert s11.Peek(11) == 0x316;
      assert s11.Peek(15) == 0xe3;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s549(s13, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 238
    * Starting at 0x10fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x111c

    requires s0.stack[5] == 0x7fe

    requires s0.stack[9] == 0x316

    requires s0.stack[13] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111c;
      assert s1.Peek(5) == 0x7fe;
      assert s1.Peek(9) == 0x316;
      assert s1.Peek(13) == 0xe3;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s550(s10, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 240
    * Starting at 0x111c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x7fe

    requires s0.stack[7] == 0x316

    requires s0.stack[11] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7fe;
      assert s1.Peek(7) == 0x316;
      assert s1.Peek(11) == 0xe3;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s551(s7, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 113
    * Starting at 0x7fe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x316

    requires s0.stack[8] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x316;
      assert s1.Peek(8) == 0xe3;
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

  /** Node 552
    * Segment Id for this node is: 114
    * Starting at 0x807
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x807 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x316

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x316;
      assert s1.Peek(7) == 0xe3;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push0(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x316;
      assert s11.Peek(10) == 0xe3;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push0(s18);
      var s20 := Keccak256(s19);
      var s21 := Push0(s20);
      assert s21.Peek(6) == 0x316;
      assert s21.Peek(10) == 0xe3;
      var s22 := Dup5(s21);
      var s23 := Push20(s22, 0xffffffffffffffffffffffffffffffffffffffff);
      var s24 := And(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x316;
      assert s31.Peek(10) == 0xe3;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Dup2(s37);
      var s39 := Swap1(s38);
      var s40 := SStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s553(s41, gas - 1)
  }

  /** Node 553
    * Segment Id for this node is: 115
    * Starting at 0x885
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x885 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x316

    requires s0.stack[7] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x316;
      assert s1.Peek(8) == 0xe3;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Dup4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push32(s6, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x08e1);
      assert s11.Peek(0) == 0x8e1;
      assert s11.Peek(9) == 0x316;
      assert s11.Peek(13) == 0xe3;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0d28);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s554(s15, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 178
    * Starting at 0xd28
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x8e1

    requires s0.stack[9] == 0x316

    requires s0.stack[13] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8e1;
      assert s1.Peek(9) == 0x316;
      assert s1.Peek(13) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d3b);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd3b;
      assert s11.Peek(5) == 0x8e1;
      assert s11.Peek(12) == 0x316;
      assert s11.Peek(16) == 0xe3;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0d19);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s555(s14, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 176
    * Starting at 0xd19
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xd3b

    requires s0.stack[6] == 0x8e1

    requires s0.stack[13] == 0x316

    requires s0.stack[17] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd3b;
      assert s1.Peek(6) == 0x8e1;
      assert s1.Peek(13) == 0x316;
      assert s1.Peek(17) == 0xe3;
      var s2 := Push2(s1, 0x0d22);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0c75);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s556(s5, gas - 1)
  }

  /** Node 556
    * Segment Id for this node is: 158
    * Starting at 0xc75
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc75 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xd22

    requires s0.stack[4] == 0xd3b

    requires s0.stack[8] == 0x8e1

    requires s0.stack[15] == 0x316

    requires s0.stack[19] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xd22;
      assert s1.Peek(4) == 0xd3b;
      assert s1.Peek(8) == 0x8e1;
      assert s1.Peek(15) == 0x316;
      assert s1.Peek(19) == 0xe3;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s557(s9, gas - 1)
  }

  /** Node 557
    * Segment Id for this node is: 177
    * Starting at 0xd22
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s557(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0xd3b

    requires s0.stack[7] == 0x8e1

    requires s0.stack[14] == 0x316

    requires s0.stack[18] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd3b;
      assert s1.Peek(7) == 0x8e1;
      assert s1.Peek(14) == 0x316;
      assert s1.Peek(18) == 0xe3;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s558(s6, gas - 1)
  }

  /** Node 558
    * Segment Id for this node is: 179
    * Starting at 0xd3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s558(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x8e1

    requires s0.stack[10] == 0x316

    requires s0.stack[14] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8e1;
      assert s1.Peek(10) == 0x316;
      assert s1.Peek(14) == 0xe3;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s559(s6, gas - 1)
  }

  /** Node 559
    * Segment Id for this node is: 116
    * Starting at 0x8e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s559(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x316

    requires s0.stack[11] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x316;
      assert s1.Peek(11) == 0xe3;
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
      assert s11.Peek(0) == 0x316;
      assert s11.Peek(4) == 0xe3;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s560(s12, gas - 1)
  }

  /** Node 560
    * Segment Id for this node is: 68
    * Starting at 0x316
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s560(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x316 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xe3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe3;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s561(s9, gas - 1)
  }

  /** Node 561
    * Segment Id for this node is: 22
    * Starting at 0xe3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s561(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00f0);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d00);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s562(s8, gas - 1)
  }

  /** Node 562
    * Segment Id for this node is: 174
    * Starting at 0xd00
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s562(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd00 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf0;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d13);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0xd13;
      assert s11.Peek(5) == 0xf0;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0cf1);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s563(s14, gas - 1)
  }

  /** Node 563
    * Segment Id for this node is: 172
    * Starting at 0xcf1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s563(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xd13

    requires s0.stack[6] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd13;
      assert s1.Peek(6) == 0xf0;
      var s2 := Push2(s1, 0x0cfa);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0ce6);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s564(s5, gas - 1)
  }

  /** Node 564
    * Segment Id for this node is: 171
    * Starting at 0xce6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s564(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xcfa

    requires s0.stack[4] == 0xd13

    requires s0.stack[8] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcfa;
      assert s1.Peek(4) == 0xd13;
      assert s1.Peek(8) == 0xf0;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := IsZero(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s565(s11, gas - 1)
  }

  /** Node 565
    * Segment Id for this node is: 173
    * Starting at 0xcfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s565(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd13

    requires s0.stack[7] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd13;
      assert s1.Peek(7) == 0xf0;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s566(s6, gas - 1)
  }

  /** Node 566
    * Segment Id for this node is: 175
    * Starting at 0xd13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s566(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s567(s6, gas - 1)
  }

  /** Node 567
    * Segment Id for this node is: 23
    * Starting at 0xf0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s567(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0 as nat
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

  /** Node 568
    * Segment Id for this node is: 17
    * Starting at 0xab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s568(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b3);
      var s3 := Push2(s2, 0x0273);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s569(s4, gas - 1)
  }

  /** Node 569
    * Segment Id for this node is: 57
    * Starting at 0x273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s569(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb3;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0282);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0e5b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s570(s9, gas - 1)
  }

  /** Node 570
    * Segment Id for this node is: 204
    * Starting at 0xe5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s570(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x282

    requires s0.stack[4] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x282;
      assert s1.Peek(4) == 0xb3;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x282;
      assert s11.Peek(7) == 0xb3;
      var s12 := Push2(s11, 0x0e72);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s572(s13, gas - 1)
      else
        ExecuteFromCFGNode_s571(s13, gas - 1)
  }

  /** Node 571
    * Segment Id for this node is: 205
    * Starting at 0xe6c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s571(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x282

    requires s0.stack[6] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x282;
      assert s1.Peek(7) == 0xb3;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s572(s5, gas - 1)
  }

  /** Node 572
    * Segment Id for this node is: 206
    * Starting at 0xe72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s572(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x282

    requires s0.stack[6] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x282;
      assert s1.Peek(6) == 0xb3;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0e85);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s575(s8, gas - 1)
      else
        ExecuteFromCFGNode_s573(s8, gas - 1)
  }

  /** Node 573
    * Segment Id for this node is: 207
    * Starting at 0xe7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s573(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x282

    requires s0.stack[6] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e84);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x282;
      assert s1.Peek(7) == 0xb3;
      var s2 := Push2(s1, 0x0e2e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s574(s3, gas - 1)
  }

  /** Node 574
    * Segment Id for this node is: 203
    * Starting at 0xe2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s574(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0xe84

    requires s0.stack[4] == 0x282

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x282;
      assert s1.Peek(7) == 0xb3;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 575
    * Segment Id for this node is: 209
    * Starting at 0xe85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s575(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x282

    requires s0.stack[6] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x282;
      assert s1.Peek(6) == 0xb3;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s576(s6, gas - 1)
  }

  /** Node 576
    * Segment Id for this node is: 58
    * Starting at 0x282
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s576(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x282 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb3;
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
      assert s11.Peek(4) == 0xb3;
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
      assert s21.Peek(5) == 0xb3;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x02ae);
      assert s31.Peek(0) == 0x2ae;
      assert s31.Peek(8) == 0xb3;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x0e5b);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s577(s34, gas - 1)
  }

  /** Node 577
    * Segment Id for this node is: 204
    * Starting at 0xe5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s577(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x2ae

    requires s0.stack[8] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2ae;
      assert s1.Peek(8) == 0xb3;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup3(s3);
      var s5 := Div(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x2ae;
      assert s11.Peek(11) == 0xb3;
      var s12 := Push2(s11, 0x0e72);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s579(s13, gas - 1)
      else
        ExecuteFromCFGNode_s578(s13, gas - 1)
  }

  /** Node 578
    * Segment Id for this node is: 205
    * Starting at 0xe6c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s578(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ae

    requires s0.stack[10] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x2ae;
      assert s1.Peek(11) == 0xb3;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s579(s5, gas - 1)
  }

  /** Node 579
    * Segment Id for this node is: 206
    * Starting at 0xe72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s579(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ae

    requires s0.stack[10] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ae;
      assert s1.Peek(10) == 0xb3;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0e85);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s582(s8, gas - 1)
      else
        ExecuteFromCFGNode_s580(s8, gas - 1)
  }

  /** Node 580
    * Segment Id for this node is: 207
    * Starting at 0xe7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s580(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ae

    requires s0.stack[10] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e84);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x2ae;
      assert s1.Peek(11) == 0xb3;
      var s2 := Push2(s1, 0x0e2e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s581(s3, gas - 1)
  }

  /** Node 581
    * Segment Id for this node is: 203
    * Starting at 0xe2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s581(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0xe84

    requires s0.stack[4] == 0x2ae

    requires s0.stack[11] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe84;
      assert s1.Peek(4) == 0x2ae;
      assert s1.Peek(11) == 0xb3;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push0(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x22);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push0(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 582
    * Segment Id for this node is: 209
    * Starting at 0xe85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s582(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x2ae

    requires s0.stack[10] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2ae;
      assert s1.Peek(10) == 0xb3;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s583(s6, gas - 1)
  }

  /** Node 583
    * Segment Id for this node is: 59
    * Starting at 0x2ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s583(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xb3;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x02f9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s586(s5, gas - 1)
      else
        ExecuteFromCFGNode_s584(s5, gas - 1)
  }

  /** Node 584
    * Segment Id for this node is: 60
    * Starting at 0x2b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s584(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0xb3;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x02d0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s603(s5, gas - 1)
      else
        ExecuteFromCFGNode_s585(s5, gas - 1)
  }

  /** Node 585
    * Segment Id for this node is: 61
    * Starting at 0x2bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s585(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0xb3;
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
      assert s11.Peek(7) == 0xb3;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x02f9);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s586(s14, gas - 1)
  }

  /** Node 586
    * Segment Id for this node is: 65
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s586(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xb3;
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
      ExecuteFromCFGNode_s587(s10, gas - 1)
  }

  /** Node 587
    * Segment Id for this node is: 18
    * Starting at 0xb3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s587(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00c0);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0bf7);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s588(s8, gas - 1)
  }

  /** Node 588
    * Segment Id for this node is: 146
    * Starting at 0xbf7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s588(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc0;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0xc0;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0c0f);
      var s16 := Dup2(s15);
      var s17 := Dup5(s16);
      var s18 := Push2(s17, 0x0bbf);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s589(s19, gas - 1)
  }

  /** Node 589
    * Segment Id for this node is: 141
    * Starting at 0xbbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s589(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xc0f

    requires s0.stack[6] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc0f;
      assert s1.Peek(6) == 0xc0;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0bc9);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0b6d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s590(s6, gas - 1)
  }

  /** Node 590
    * Segment Id for this node is: 134
    * Starting at 0xb6d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s590(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xbc9

    requires s0.stack[5] == 0xc0f

    requires s0.stack[9] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbc9;
      assert s1.Peek(5) == 0xc0f;
      assert s1.Peek(9) == 0xc0;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s591(s10, gas - 1)
  }

  /** Node 591
    * Segment Id for this node is: 142
    * Starting at 0xbc9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s591(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xc0f

    requires s0.stack[8] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc0f;
      assert s1.Peek(8) == 0xc0;
      var s2 := Push2(s1, 0x0bd3);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0b77);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s592(s6, gas - 1)
  }

  /** Node 592
    * Segment Id for this node is: 135
    * Starting at 0xb77
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s592(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xbd3

    requires s0.stack[7] == 0xc0f

    requires s0.stack[11] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbd3;
      assert s1.Peek(7) == 0xc0f;
      assert s1.Peek(11) == 0xc0;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0xbd3;
      assert s11.Peek(8) == 0xc0f;
      assert s11.Peek(12) == 0xc0;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s593(s15, gas - 1)
  }

  /** Node 593
    * Segment Id for this node is: 143
    * Starting at 0xbd3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s593(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xc0f

    requires s0.stack[9] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc0f;
      assert s1.Peek(9) == 0xc0;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0be3);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0b87);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s594(s11, gas - 1)
  }

  /** Node 594
    * Segment Id for this node is: 136
    * Starting at 0xb87
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s594(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xbe3

    requires s0.stack[8] == 0xc0f

    requires s0.stack[12] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbe3;
      assert s1.Peek(8) == 0xc0f;
      assert s1.Peek(12) == 0xc0;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s595(s2, gas - 1)
  }

  /** Node 595
    * Segment Id for this node is: 137
    * Starting at 0xb89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s595(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbe3

    requires s0.stack[9] == 0xc0f

    requires s0.stack[13] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbe3;
      assert s1.Peek(9) == 0xc0f;
      assert s1.Peek(13) == 0xc0;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ba4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s597(s7, gas - 1)
      else
        ExecuteFromCFGNode_s596(s7, gas - 1)
  }

  /** Node 596
    * Segment Id for this node is: 138
    * Starting at 0xb92
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s596(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbe3

    requires s0.stack[9] == 0xc0f

    requires s0.stack[13] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0xbe3;
      assert s1.Peek(10) == 0xc0f;
      assert s1.Peek(14) == 0xc0;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xbe3;
      assert s11.Peek(10) == 0xc0f;
      assert s11.Peek(14) == 0xc0;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Push2(s13, 0x0b89);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s595(s15, gas - 1)
  }

  /** Node 597
    * Segment Id for this node is: 139
    * Starting at 0xba4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s597(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xbe3

    requires s0.stack[9] == 0xc0f

    requires s0.stack[13] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbe3;
      assert s1.Peek(9) == 0xc0f;
      assert s1.Peek(13) == 0xc0;
      var s2 := Push0(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s598(s11, gas - 1)
  }

  /** Node 598
    * Segment Id for this node is: 144
    * Starting at 0xbe3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s598(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xc0f

    requires s0.stack[8] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc0f;
      assert s1.Peek(8) == 0xc0;
      var s2 := Push2(s1, 0x0bec);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0baf);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s599(s5, gas - 1)
  }

  /** Node 599
    * Segment Id for this node is: 140
    * Starting at 0xbaf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s599(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbaf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xbec

    requires s0.stack[6] == 0xc0f

    requires s0.stack[10] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbec;
      assert s1.Peek(6) == 0xc0f;
      assert s1.Peek(10) == 0xc0;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0xbec;
      assert s11.Peek(7) == 0xc0f;
      assert s11.Peek(11) == 0xc0;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s600(s14, gas - 1)
  }

  /** Node 600
    * Segment Id for this node is: 145
    * Starting at 0xbec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s600(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xc0f

    requires s0.stack[9] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc0f;
      assert s1.Peek(9) == 0xc0;
      var s2 := Dup5(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s601(s11, gas - 1)
  }

  /** Node 601
    * Segment Id for this node is: 147
    * Starting at 0xc0f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s601(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xc0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xc0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s602(s8, gas - 1)
  }

  /** Node 602
    * Segment Id for this node is: 19
    * Starting at 0xc0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s602(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0 as nat
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

  /** Node 603
    * Segment Id for this node is: 62
    * Starting at 0x2d0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s603(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xb3;
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
      ExecuteFromCFGNode_s604(s11, gas - 1)
  }

  /** Node 604
    * Segment Id for this node is: 63
    * Starting at 0x2dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s604(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xb3;
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
      assert s11.Peek(7) == 0xb3;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x02dc);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s604(s16, gas - 1)
      else
        ExecuteFromCFGNode_s605(s16, gas - 1)
  }

  /** Node 605
    * Segment Id for this node is: 64
    * Starting at 0x2f0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s605(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xb3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0xb3;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s586(s8, gas - 1)
  }

  /** Node 606
    * Segment Id for this node is: 16
    * Starting at 0xa7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s606(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
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
