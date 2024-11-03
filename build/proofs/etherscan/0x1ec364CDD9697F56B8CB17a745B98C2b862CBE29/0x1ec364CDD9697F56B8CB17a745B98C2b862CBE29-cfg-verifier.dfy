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
      var s6 := Push2(s5, 0x00d4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s431(s7, gas - 1)
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
      var s6 := Push4(s5, 0x5e9d4044);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0081);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s9, gas - 1)
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
      var s2 := Push4(s1, 0xc26c12eb);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x005b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc26c12eb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ae);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc56710ff);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd6cd921e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01c9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s9(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
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
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 9
    * Segment Id for this node is: 44
    * Starting at 0x1c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x016a);
      var s3 := Push2(s2, 0x01d7);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x11f6);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s7, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 159
    * Starting at 0x11f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d7

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d7;
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x1209);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s11, gas - 1)
      else
        ExecuteFromCFGNode_s11(s11, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 160
    * Starting at 0x1205
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1205 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1d7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1d7;
      assert s1.Peek(6) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 12
    * Segment Id for this node is: 161
    * Starting at 0x1209
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1209 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1d7

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1d7;
      assert s1.Peek(5) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1220);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s9, gas - 1)
      else
        ExecuteFromCFGNode_s13(s9, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 162
    * Starting at 0x121c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1d7

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x1d7;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 163
    * Starting at 0x1220
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1220 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1d7

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1d7;
      assert s1.Peek(6) == 0x16a;
      var s2 := Push2(s1, 0x122c);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s8, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 126
    * Starting at 0x1044
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x122c

    requires s0.stack[8] == 0x1d7

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x122c;
      assert s1.Peek(8) == 0x1d7;
      assert s1.Peek(9) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x1055);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s9, gas - 1)
      else
        ExecuteFromCFGNode_s16(s9, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 127
    * Starting at 0x1051
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x122c

    requires s0.stack[9] == 0x1d7

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x122c;
      assert s1.Peek(10) == 0x1d7;
      assert s1.Peek(11) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 17
    * Segment Id for this node is: 128
    * Starting at 0x1055
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x122c

    requires s0.stack[9] == 0x1d7

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x122c;
      assert s1.Peek(9) == 0x1d7;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1070);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s10, gas - 1)
      else
        ExecuteFromCFGNode_s18(s10, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 129
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x122c

    requires s0.stack[11] == 0x1d7

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1070);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x122c;
      assert s1.Peek(12) == 0x1d7;
      assert s1.Peek(13) == 0x16a;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s3, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1070

    requires s0.stack[6] == 0x122c

    requires s0.stack[12] == 0x1d7

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x122c;
      assert s1.Peek(12) == 0x1d7;
      assert s1.Peek(13) == 0x16a;
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

  /** Node 20
    * Segment Id for this node is: 130
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x122c

    requires s0.stack[11] == 0x1d7

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x122c;
      assert s1.Peek(11) == 0x1d7;
      assert s1.Peek(12) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x122c;
      assert s11.Peek(15) == 0x1d7;
      assert s11.Peek(16) == 0x16a;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x122c;
      assert s21.Peek(16) == 0x1d7;
      assert s21.Peek(17) == 0x16a;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x10b6);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s26, gas - 1)
      else
        ExecuteFromCFGNode_s21(s26, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 131
    * Starting at 0x10af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x122c

    requires s0.stack[13] == 0x1d7

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10b6);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x122c;
      assert s1.Peek(14) == 0x1d7;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x10b6

    requires s0.stack[8] == 0x122c

    requires s0.stack[14] == 0x1d7

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x122c;
      assert s1.Peek(14) == 0x1d7;
      assert s1.Peek(15) == 0x16a;
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

  /** Node 23
    * Segment Id for this node is: 132
    * Starting at 0x10b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x122c

    requires s0.stack[13] == 0x1d7

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x122c;
      assert s1.Peek(13) == 0x1d7;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x122c;
      assert s11.Peek(17) == 0x1d7;
      assert s11.Peek(18) == 0x16a;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s17, gas - 1)
      else
        ExecuteFromCFGNode_s24(s17, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 133
    * Starting at 0x10cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x122c

    requires s0.stack[13] == 0x1d7

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x122c;
      assert s1.Peek(14) == 0x1d7;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 134
    * Starting at 0x10cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x122c

    requires s0.stack[13] == 0x1d7

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x122c;
      assert s1.Peek(13) == 0x1d7;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x122c;
      assert s11.Peek(15) == 0x1d7;
      assert s11.Peek(16) == 0x16a;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x122c;
      assert s21.Peek(11) == 0x1d7;
      assert s21.Peek(12) == 0x16a;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s28, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 164
    * Starting at 0x122c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x122c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1d7

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1d7;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push2(s8, 0x1184);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x11d4);
      assert s11.Peek(0) == 0x11d4;
      assert s11.Peek(2) == 0x1184;
      assert s11.Peek(8) == 0x1d7;
      assert s11.Peek(9) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s12, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 157
    * Starting at 0x11d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1184

    requires s0.stack[7] == 0x1d7

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1184;
      assert s1.Peek(7) == 0x1d7;
      assert s1.Peek(8) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s8, gas - 1)
      else
        ExecuteFromCFGNode_s28(s8, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 158
    * Starting at 0x11f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1184

    requires s0.stack[7] == 0x1d7

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1184;
      assert s1.Peek(8) == 0x1d7;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 29
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1184

    requires s0.stack[7] == 0x1d7

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1184;
      assert s1.Peek(7) == 0x1d7;
      assert s1.Peek(8) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s3, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 150
    * Starting at 0x1184
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1184 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1d7

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1d7;
      assert s1.Peek(6) == 0x16a;
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
      ExecuteFromCFGNode_s31(s11, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 45
    * Starting at 0x1d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0aec);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s3, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 98
    * Starting at 0xaec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0b2a);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x02b6);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x2b6;
      assert s11.Peek(4) == 0xb2a;
      assert s11.Peek(7) == 0x16a;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s21, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 53
    * Starting at 0x2b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xb2a

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2a;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0xb2a;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0cf3);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s21, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 108
    * Starting at 0xcf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xb2a

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb2a;
      assert s1.Peek(4) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xb2a;
      assert s11.Peek(9) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0xb2a;
      assert s21.Peek(7) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0xb2a;
      assert s31.Peek(12) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0d67);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s41, gas - 1)
      else
        ExecuteFromCFGNode_s35(s41, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 109
    * Starting at 0xd5e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0xb2a

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xb2a;
      assert s1.Peek(10) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 36
    * Segment Id for this node is: 110
    * Starting at 0xd67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0xb2a

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xb2a;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(6) == 0xb2a;
      assert s11.Peek(9) == 0x16a;
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
      assert s21.Peek(5) == 0xb2a;
      assert s21.Peek(8) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12af);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s28, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 175
    * Starting at 0x12af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0xb2a

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0xb2a;
      assert s1.Peek(8) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s10, gas - 1)
      else
        ExecuteFromCFGNode_s38(s10, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 176
    * Starting at 0x12bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xb2a

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xb2a;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 39
    * Segment Id for this node is: 177
    * Starting at 0x12c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xb2a

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0xb2a;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x112c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 141
    * Starting at 0x112c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xb2a

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xb2a;
      assert s1.Peek(12) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s8, gas - 1)
      else
        ExecuteFromCFGNode_s41(s8, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 142
    * Starting at 0x1136
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xb2a

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0xb2a;
      assert s1.Peek(13) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 42
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xb2a

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xb2a;
      assert s1.Peek(12) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s3, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0xb2a

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xb2a;
      assert s1.Peek(10) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xb2a

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb2a;
      assert s1.Peek(6) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s6, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 99
    * Starting at 0xb2a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0c27);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s4, gas - 1)
      else
        ExecuteFromCFGNode_s46(s4, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 100
    * Starting at 0xb30
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0b84);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xb84;
      assert s11.Peek(5) == 0x16a;
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push32(s17, 0x726f636b657444414f50726f746f636f6c50726f706f73616c73000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0xb84;
      assert s21.Peek(5) == 0x16a;
      var s22 := Push2(s21, 0x0d8b);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s23, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 111
    * Starting at 0xd8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xb84

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb84;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0da2);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x027b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x27b;
      assert s11.Peek(3) == 0xda2;
      assert s11.Peek(7) == 0xb84;
      assert s11.Peek(11) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x12cc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s14, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 178
    * Starting at 0x12cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x27b

    requires s0.stack[3] == 0xda2

    requires s0.stack[7] == 0xb84

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x27b;
      assert s1.Peek(3) == 0xda2;
      assert s1.Peek(7) == 0xb84;
      assert s1.Peek(11) == 0x16a;
      var s2 := Push32(s1, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x128b);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x128b;
      assert s11.Peek(7) == 0x27b;
      assert s11.Peek(8) == 0xda2;
      assert s11.Peek(12) == 0xb84;
      assert s11.Peek(16) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s12, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x128b

    requires s0.stack[6] == 0x27b

    requires s0.stack[7] == 0xda2

    requires s0.stack[11] == 0xb84

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(6) == 0x27b;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0xb84;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0xb84

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x27b;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0xb84;
      assert s1.Peek(18) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s7, gas - 1)
      else
        ExecuteFromCFGNode_s51(s7, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0xb84

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x128b;
      assert s1.Peek(10) == 0x27b;
      assert s1.Peek(11) == 0xda2;
      assert s1.Peek(15) == 0xb84;
      assert s1.Peek(19) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x128b;
      assert s11.Peek(10) == 0x27b;
      assert s11.Peek(11) == 0xda2;
      assert s11.Peek(15) == 0xb84;
      assert s11.Peek(19) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s14, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0xb84

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x27b;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0xb84;
      assert s1.Peek(18) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x128b;
      assert s11.Peek(6) == 0x27b;
      assert s11.Peek(7) == 0xda2;
      assert s11.Peek(11) == 0xb84;
      assert s11.Peek(15) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s14, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x27b

    requires s0.stack[5] == 0xda2

    requires s0.stack[9] == 0xb84

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x27b;
      assert s1.Peek(5) == 0xda2;
      assert s1.Peek(9) == 0xb84;
      assert s1.Peek(13) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s7, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 50
    * Starting at 0x27b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xda2

    requires s0.stack[5] == 0xb84

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda2;
      assert s1.Peek(5) == 0xb84;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(2) == 0xda2;
      assert s11.Peek(6) == 0xb84;
      assert s11.Peek(10) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0c5b);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s21, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 105
    * Starting at 0xc5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xda2

    requires s0.stack[5] == 0xb84

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda2;
      assert s1.Peek(5) == 0xb84;
      assert s1.Peek(9) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xda2;
      assert s11.Peek(10) == 0xb84;
      assert s11.Peek(14) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0xda2;
      assert s21.Peek(8) == 0xb84;
      assert s21.Peek(12) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0xda2;
      assert s31.Peek(13) == 0xb84;
      assert s31.Peek(17) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0ccf);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s41, gas - 1)
      else
        ExecuteFromCFGNode_s56(s41, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 106
    * Starting at 0xcc6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0xb84

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0xb84;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 57
    * Segment Id for this node is: 107
    * Starting at 0xccf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0xb84

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xda2;
      assert s1.Peek(10) == 0xb84;
      assert s1.Peek(14) == 0x16a;
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
      assert s11.Peek(6) == 0xda2;
      assert s11.Peek(10) == 0xb84;
      assert s11.Peek(14) == 0x16a;
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
      assert s21.Peek(5) == 0xda2;
      assert s21.Peek(9) == 0xb84;
      assert s21.Peek(13) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1292);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s28, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 172
    * Starting at 0x1292
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0xda2

    requires s0.stack[9] == 0xb84

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0xda2;
      assert s1.Peek(9) == 0xb84;
      assert s1.Peek(13) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12a4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s10, gas - 1)
      else
        ExecuteFromCFGNode_s59(s10, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 173
    * Starting at 0x12a0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0xb84

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0xb84;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 60
    * Segment Id for this node is: 174
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0xb84

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0xda2;
      assert s1.Peek(10) == 0xb84;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x11d4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s7, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 157
    * Starting at 0x11d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0xb84

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xda2;
      assert s1.Peek(13) == 0xb84;
      assert s1.Peek(17) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s8, gas - 1)
      else
        ExecuteFromCFGNode_s62(s8, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 158
    * Starting at 0x11f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0xb84

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0xb84;
      assert s1.Peek(18) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 63
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0xb84

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xda2;
      assert s1.Peek(13) == 0xb84;
      assert s1.Peek(17) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s3, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0xda2

    requires s0.stack[11] == 0xb84

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0xb84;
      assert s1.Peek(15) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s7, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xda2

    requires s0.stack[7] == 0xb84

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xda2;
      assert s1.Peek(7) == 0xb84;
      assert s1.Peek(11) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 112
    * Starting at 0xda2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xb84

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb84;
      assert s1.Peek(8) == 0x16a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x0296);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s8, gas - 1)
      else
        ExecuteFromCFGNode_s67(s8, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 113
    * Starting at 0xdc0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xb84

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xb84;
      assert s1.Peek(8) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x12);
      assert s11.Peek(5) == 0xb84;
      assert s11.Peek(9) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0xb84;
      assert s21.Peek(9) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s24, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 59
    * Starting at 0x408
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xb84

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb84;
      assert s1.Peek(8) == 0x16a;
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

  /** Node 69
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xb84

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb84;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s6, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 101
    * Starting at 0xb84
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb84 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0c27);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s6, gas - 1)
      else
        ExecuteFromCFGNode_s71(s6, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 102
    * Starting at 0xba0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x39);
      assert s11.Peek(4) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f6e6c792044414f2050726f746f636f6c2050726f706f73616c7320636f6e74);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x726163742063616e2075706461746520612073657474696e6700000000000000);
      assert s21.Peek(4) == 0x16a;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x0408);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s29, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 59
    * Starting at 0x408
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
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

  /** Node 73
    * Segment Id for this node is: 103
    * Starting at 0xc27
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc27 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0445);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0c3f);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0xc3f;
      assert s11.Peek(4) == 0x445;
      assert s11.Peek(7) == 0x16a;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x126d);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s15, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xc3f

    requires s0.stack[4] == 0x445

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc3f;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0xc3f;
      assert s11.Peek(9) == 0x445;
      assert s11.Peek(12) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s12, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0xc3f

    requires s0.stack[8] == 0x445

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0xc3f;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(11) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s5, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xc3f

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0xc3f;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s7, gas - 1)
      else
        ExecuteFromCFGNode_s77(s7, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xc3f

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0xc3f;
      assert s1.Peek(12) == 0x445;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0xc3f;
      assert s11.Peek(12) == 0x445;
      assert s11.Peek(15) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s14, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xc3f

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0xc3f;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(14) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0xc3f;
      assert s11.Peek(8) == 0x445;
      assert s11.Peek(11) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s14, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xc3f

    requires s0.stack[6] == 0x445

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xc3f;
      assert s1.Peek(6) == 0x445;
      assert s1.Peek(9) == 0x16a;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s8, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 104
    * Starting at 0xc3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x445

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x445;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0x445;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup3(s19);
      var s21 := Push2(s20, 0x0fb0);
      assert s21.Peek(0) == 0xfb0;
      assert s21.Peek(3) == 0x445;
      assert s21.Peek(6) == 0x16a;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s22, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 124
    * Starting at 0xfb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x445

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x445;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xca446dd900000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x445;
      assert s11.Peek(8) == 0x16a;
      var s12 := Dup5(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push20(s14, 0xffffffffffffffffffffffffffffffffffffffff);
      var s16 := Dup4(s15);
      var s17 := Dup2(s16);
      var s18 := And(s17);
      var s19 := Push1(s18, 0x24);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x445;
      assert s21.Peek(10) == 0x16a;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x0100);
      var s24 := Swap1(s23);
      var s25 := Swap3(s24);
      var s26 := Div(s25);
      var s27 := Swap1(s26);
      var s28 := Swap2(s27);
      var s29 := And(s28);
      var s30 := Swap1(s29);
      var s31 := Push4(s30, 0xca446dd9);
      assert s31.Peek(5) == 0x445;
      assert s31.Peek(8) == 0x16a;
      var s32 := Swap1(s31);
      var s33 := Push1(s32, 0x44);
      var s34 := Add(s33);
      var s35 := Push2(s34, 0x0e80);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s36, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 115
    * Starting at 0xe80
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x445

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x445;
      assert s1.Peek(8) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup8(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(12) == 0x445;
      assert s11.Peek(15) == 0x16a;
      var s12 := ExtCodeSize(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0e9a);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s17, gas - 1)
      else
        ExecuteFromCFGNode_s83(s17, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 116
    * Starting at 0xe96
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x445

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x445;
      assert s1.Peek(16) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 84
    * Segment Id for this node is: 117
    * Starting at 0xe9a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x445

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x445;
      assert s1.Peek(15) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0eae);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s9, gas - 1)
      else
        ExecuteFromCFGNode_s85(s9, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 118
    * Starting at 0xea5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x445

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x445;
      assert s1.Peek(10) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 86
    * Segment Id for this node is: 119
    * Starting at 0xeae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x445

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x445;
      assert s1.Peek(9) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s8, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 62
    * Starting at 0x445
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x445 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s4, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 34
    * Starting at 0x16a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a as nat
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

  /** Node 89
    * Segment Id for this node is: 42
    * Starting at 0x1b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e1);
      var s3 := Push2(s2, 0x01c4);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10ef);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 135
    * Starting at 0x10ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1c4

    requires s0.stack[3] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c4;
      assert s1.Peek(3) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1101);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s10, gas - 1)
      else
        ExecuteFromCFGNode_s91(s10, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 136
    * Starting at 0x10fd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1c4

    requires s0.stack[4] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1c4;
      assert s1.Peek(5) == 0xe1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 92
    * Segment Id for this node is: 137
    * Starting at 0x1101
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1c4

    requires s0.stack[4] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c4;
      assert s1.Peek(4) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1118);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s9, gas - 1)
      else
        ExecuteFromCFGNode_s93(s9, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 138
    * Starting at 0x1114
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c4

    requires s0.stack[5] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1c4;
      assert s1.Peek(6) == 0xe1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 94
    * Segment Id for this node is: 139
    * Starting at 0x1118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c4

    requires s0.stack[5] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c4;
      assert s1.Peek(5) == 0xe1;
      var s2 := Push2(s1, 0x1124);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s8, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 126
    * Starting at 0x1044
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x1c4

    requires s0.stack[8] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x1c4;
      assert s1.Peek(8) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x1055);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s9, gas - 1)
      else
        ExecuteFromCFGNode_s96(s9, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 127
    * Starting at 0x1051
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1124

    requires s0.stack[8] == 0x1c4

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1124;
      assert s1.Peek(9) == 0x1c4;
      assert s1.Peek(10) == 0xe1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 97
    * Segment Id for this node is: 128
    * Starting at 0x1055
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1124

    requires s0.stack[8] == 0x1c4

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1124;
      assert s1.Peek(8) == 0x1c4;
      assert s1.Peek(9) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1070);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s10, gas - 1)
      else
        ExecuteFromCFGNode_s98(s10, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 129
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x1c4

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1070);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x1c4;
      assert s1.Peek(12) == 0xe1;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s3, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1070

    requires s0.stack[6] == 0x1124

    requires s0.stack[11] == 0x1c4

    requires s0.stack[12] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x1c4;
      assert s1.Peek(12) == 0xe1;
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

  /** Node 100
    * Segment Id for this node is: 130
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x1c4

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x1c4;
      assert s1.Peek(11) == 0xe1;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x1124;
      assert s11.Peek(14) == 0x1c4;
      assert s11.Peek(15) == 0xe1;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x1124;
      assert s21.Peek(15) == 0x1c4;
      assert s21.Peek(16) == 0xe1;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x10b6);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s26, gas - 1)
      else
        ExecuteFromCFGNode_s101(s26, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 131
    * Starting at 0x10af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x1c4

    requires s0.stack[13] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10b6);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x1c4;
      assert s1.Peek(14) == 0xe1;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s3, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x10b6

    requires s0.stack[8] == 0x1124

    requires s0.stack[13] == 0x1c4

    requires s0.stack[14] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x1c4;
      assert s1.Peek(14) == 0xe1;
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

  /** Node 103
    * Segment Id for this node is: 132
    * Starting at 0x10b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x1c4

    requires s0.stack[13] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1124;
      assert s1.Peek(12) == 0x1c4;
      assert s1.Peek(13) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1124;
      assert s11.Peek(16) == 0x1c4;
      assert s11.Peek(17) == 0xe1;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s17, gas - 1)
      else
        ExecuteFromCFGNode_s104(s17, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 133
    * Starting at 0x10cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x1c4

    requires s0.stack[13] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x1c4;
      assert s1.Peek(14) == 0xe1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 105
    * Segment Id for this node is: 134
    * Starting at 0x10cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x1c4

    requires s0.stack[13] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1124;
      assert s1.Peek(12) == 0x1c4;
      assert s1.Peek(13) == 0xe1;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x1124;
      assert s11.Peek(14) == 0x1c4;
      assert s11.Peek(15) == 0xe1;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1124;
      assert s21.Peek(10) == 0x1c4;
      assert s21.Peek(11) == 0xe1;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s28, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c4

    requires s0.stack[6] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c4;
      assert s1.Peek(6) == 0xe1;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s8, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 43
    * Starting at 0x1c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe1;
      var s2 := Push2(s1, 0x0ab7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s3, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 96
    * Starting at 0xab7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0296);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0ad1);
      assert s11.Peek(0) == 0xad1;
      assert s11.Peek(4) == 0x296;
      assert s11.Peek(7) == 0xe1;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x126d);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s16, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xad1

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xad1;
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xe1;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0xad1;
      assert s11.Peek(9) == 0x296;
      assert s11.Peek(12) == 0xe1;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s12, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0xad1

    requires s0.stack[8] == 0x296

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0xad1;
      assert s1.Peek(8) == 0x296;
      assert s1.Peek(11) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s111(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xad1

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0xad1;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s7, gas - 1)
      else
        ExecuteFromCFGNode_s112(s7, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xad1

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0xad1;
      assert s1.Peek(12) == 0x296;
      assert s1.Peek(15) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0xad1;
      assert s11.Peek(12) == 0x296;
      assert s11.Peek(15) == 0xe1;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xad1

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0xad1;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0xe1;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0xad1;
      assert s11.Peek(8) == 0x296;
      assert s11.Peek(11) == 0xe1;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s14, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xad1

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xad1;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xe1;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s8, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 97
    * Starting at 0xad1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0xe1;
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
      assert s11.Peek(2) == 0x296;
      assert s11.Peek(5) == 0xe1;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0f18);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s21, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 121
    * Starting at 0xf18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0xbd02d0f500000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0xe1;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x296;
      assert s21.Peek(7) == 0xe1;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0xbd02d0f5);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x296;
      assert s31.Peek(12) == 0xe1;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0f8c);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s41, gas - 1)
      else
        ExecuteFromCFGNode_s117(s41, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 122
    * Starting at 0xf83
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 118
    * Segment Id for this node is: 123
    * Starting at 0xf8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xe1;
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
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0xe1;
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
      assert s21.Peek(5) == 0x296;
      assert s21.Peek(8) == 0xe1;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12fe);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s28, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 179
    * Starting at 0x12fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x296

    requires s0.stack[8] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x296;
      assert s1.Peek(8) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1310);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s10, gas - 1)
      else
        ExecuteFromCFGNode_s120(s10, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 180
    * Starting at 0x130c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x130c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0xe1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 121
    * Segment Id for this node is: 181
    * Starting at 0x1310
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1310 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xe1;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0xe1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 23
    * Starting at 0xe1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe1 as nat
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
      ExecuteFromCFGNode_s125(s8, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 24
    * Starting at 0xeb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
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
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 126
    * Segment Id for this node is: 41
    * Starting at 0x1ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e1);
      var s3 := Push2(s2, 0x0a7b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s4, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 95
    * Starting at 0xa7b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x021c);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(4) == 0xe1;
      var s12 := Push1(s11, 0x0e);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6d656d626572732e71756f72756d000000000000000000000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s128(s20, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 96
    * Starting at 0xab7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x21c

    requires s0.stack[3] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x21c;
      assert s1.Peek(3) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0296);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0ad1);
      assert s11.Peek(0) == 0xad1;
      assert s11.Peek(4) == 0x296;
      assert s11.Peek(7) == 0x21c;
      assert s11.Peek(9) == 0xe1;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x126d);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s16, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xad1

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x21c

    requires s0.stack[9] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xad1;
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x21c;
      assert s1.Peek(9) == 0xe1;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0xad1;
      assert s11.Peek(9) == 0x296;
      assert s11.Peek(12) == 0x21c;
      assert s11.Peek(14) == 0xe1;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s12, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0xad1

    requires s0.stack[8] == 0x296

    requires s0.stack[11] == 0x21c

    requires s0.stack[13] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0xad1;
      assert s1.Peek(8) == 0x296;
      assert s1.Peek(11) == 0x21c;
      assert s1.Peek(13) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s131(s5, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xad1

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x21c

    requires s0.stack[16] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0xad1;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0x21c;
      assert s1.Peek(16) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s7, gas - 1)
      else
        ExecuteFromCFGNode_s132(s7, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xad1

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x21c

    requires s0.stack[16] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0xad1;
      assert s1.Peek(12) == 0x296;
      assert s1.Peek(15) == 0x21c;
      assert s1.Peek(17) == 0xe1;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0xad1;
      assert s11.Peek(12) == 0x296;
      assert s11.Peek(15) == 0x21c;
      assert s11.Peek(17) == 0xe1;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s14, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0xad1

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x21c

    requires s0.stack[16] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0xad1;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0x21c;
      assert s1.Peek(16) == 0xe1;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0xad1;
      assert s11.Peek(8) == 0x296;
      assert s11.Peek(11) == 0x21c;
      assert s11.Peek(13) == 0xe1;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s14, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xad1

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x21c

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xad1;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x21c;
      assert s1.Peek(11) == 0xe1;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s8, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 97
    * Starting at 0xad1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0x21c

    requires s0.stack[6] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0x21c;
      assert s1.Peek(6) == 0xe1;
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
      assert s11.Peek(2) == 0x296;
      assert s11.Peek(5) == 0x21c;
      assert s11.Peek(7) == 0xe1;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0f18);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s21, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 121
    * Starting at 0xf18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0x21c

    requires s0.stack[6] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0x21c;
      assert s1.Peek(6) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0xbd02d0f500000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0x21c;
      assert s11.Peek(11) == 0xe1;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x296;
      assert s21.Peek(7) == 0x21c;
      assert s21.Peek(9) == 0xe1;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0xbd02d0f5);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x296;
      assert s31.Peek(12) == 0x21c;
      assert s31.Peek(14) == 0xe1;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0f8c);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s41, gas - 1)
      else
        ExecuteFromCFGNode_s137(s41, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 122
    * Starting at 0xf83
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x21c

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x21c;
      assert s1.Peek(12) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 138
    * Segment Id for this node is: 123
    * Starting at 0xf8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x21c

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x21c;
      assert s1.Peek(11) == 0xe1;
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
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0x21c;
      assert s11.Peek(11) == 0xe1;
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
      assert s21.Peek(5) == 0x296;
      assert s21.Peek(8) == 0x21c;
      assert s21.Peek(10) == 0xe1;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12fe);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s28, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 179
    * Starting at 0x12fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x296

    requires s0.stack[8] == 0x21c

    requires s0.stack[10] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x296;
      assert s1.Peek(8) == 0x21c;
      assert s1.Peek(10) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1310);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s10, gas - 1)
      else
        ExecuteFromCFGNode_s140(s10, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 180
    * Starting at 0x130c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x130c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x21c

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x21c;
      assert s1.Peek(12) == 0xe1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 141
    * Segment Id for this node is: 181
    * Starting at 0x1310
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1310 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x21c

    requires s0.stack[11] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x21c;
      assert s1.Peek(11) == 0xe1;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s7, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x21c

    requires s0.stack[8] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x21c;
      assert s1.Peek(8) == 0xe1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s6, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x21c

    requires s0.stack[5] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x21c;
      assert s1.Peek(5) == 0xe1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s6, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 47
    * Starting at 0x21c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe1;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s5, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 9
    * Starting at 0x5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x5e9d4044);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x018b);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s6, gas - 1)
      else
        ExecuteFromCFGNode_s146(s6, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 10
    * Starting at 0x67
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x75bb09c6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x019e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s5, gas - 1)
      else
        ExecuteFromCFGNode_s147(s5, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa8301dbc);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01a6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s5, gas - 1)
      else
        ExecuteFromCFGNode_s148(s5, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
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

  /** Node 149
    * Segment Id for this node is: 40
    * Starting at 0x1a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e1);
      var s3 := Push2(s2, 0x0a3b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s4, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 94
    * Starting at 0xa3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x021c);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(4) == 0xe1;
      var s12 := Push1(s11, 0x12);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x70726f706f73616c2e766f74652e74696d650000000000000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0ab7);
      assert s21.Peek(0) == 0xab7;
      assert s21.Peek(2) == 0x21c;
      assert s21.Peek(4) == 0xe1;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s22, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 39
    * Starting at 0x19e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e1);
      var s3 := Push2(s2, 0x09fb);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s4, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 93
    * Starting at 0x9fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x021c);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(4) == 0xe1;
      var s12 := Push1(s11, 0x14);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x70726f706f73616c2e616374696f6e2e74696d65000000000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0ab7);
      assert s21.Peek(0) == 0xab7;
      assert s21.Peek(2) == 0x21c;
      assert s21.Peek(4) == 0xe1;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s22, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 37
    * Starting at 0x18b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x016a);
      var s3 := Push2(s2, 0x0199);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x118f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s7, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 151
    * Starting at 0x118f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x199

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x199;
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x11a2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s11, gas - 1)
      else
        ExecuteFromCFGNode_s155(s11, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 152
    * Starting at 0x119e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x199

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x199;
      assert s1.Peek(6) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 156
    * Segment Id for this node is: 153
    * Starting at 0x11a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x199

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x199;
      assert s1.Peek(5) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x11b9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s9, gas - 1)
      else
        ExecuteFromCFGNode_s157(s9, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 154
    * Starting at 0x11b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x199

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x199;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 158
    * Segment Id for this node is: 155
    * Starting at 0x11b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x199

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x199;
      assert s1.Peek(6) == 0x16a;
      var s2 := Push2(s1, 0x11c5);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s8, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 126
    * Starting at 0x1044
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x11c5

    requires s0.stack[8] == 0x199

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11c5;
      assert s1.Peek(8) == 0x199;
      assert s1.Peek(9) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x1055);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s9, gas - 1)
      else
        ExecuteFromCFGNode_s160(s9, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 127
    * Starting at 0x1051
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x11c5

    requires s0.stack[9] == 0x199

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x11c5;
      assert s1.Peek(10) == 0x199;
      assert s1.Peek(11) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 161
    * Segment Id for this node is: 128
    * Starting at 0x1055
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x11c5

    requires s0.stack[9] == 0x199

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11c5;
      assert s1.Peek(9) == 0x199;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1070);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s10, gas - 1)
      else
        ExecuteFromCFGNode_s162(s10, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 129
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x11c5

    requires s0.stack[11] == 0x199

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1070);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x11c5;
      assert s1.Peek(12) == 0x199;
      assert s1.Peek(13) == 0x16a;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s3, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1070

    requires s0.stack[6] == 0x11c5

    requires s0.stack[12] == 0x199

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x11c5;
      assert s1.Peek(12) == 0x199;
      assert s1.Peek(13) == 0x16a;
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

  /** Node 164
    * Segment Id for this node is: 130
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x11c5

    requires s0.stack[11] == 0x199

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x11c5;
      assert s1.Peek(11) == 0x199;
      assert s1.Peek(12) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x11c5;
      assert s11.Peek(15) == 0x199;
      assert s11.Peek(16) == 0x16a;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x11c5;
      assert s21.Peek(16) == 0x199;
      assert s21.Peek(17) == 0x16a;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x10b6);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s26, gas - 1)
      else
        ExecuteFromCFGNode_s165(s26, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 131
    * Starting at 0x10af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x11c5

    requires s0.stack[13] == 0x199

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10b6);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x11c5;
      assert s1.Peek(14) == 0x199;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s3, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x10b6

    requires s0.stack[8] == 0x11c5

    requires s0.stack[14] == 0x199

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x11c5;
      assert s1.Peek(14) == 0x199;
      assert s1.Peek(15) == 0x16a;
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

  /** Node 167
    * Segment Id for this node is: 132
    * Starting at 0x10b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x11c5

    requires s0.stack[13] == 0x199

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x11c5;
      assert s1.Peek(13) == 0x199;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x11c5;
      assert s11.Peek(17) == 0x199;
      assert s11.Peek(18) == 0x16a;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s17, gas - 1)
      else
        ExecuteFromCFGNode_s168(s17, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 133
    * Starting at 0x10cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x11c5

    requires s0.stack[13] == 0x199

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x11c5;
      assert s1.Peek(14) == 0x199;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 169
    * Segment Id for this node is: 134
    * Starting at 0x10cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x11c5

    requires s0.stack[13] == 0x199

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x11c5;
      assert s1.Peek(13) == 0x199;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x11c5;
      assert s11.Peek(15) == 0x199;
      assert s11.Peek(16) == 0x16a;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x11c5;
      assert s21.Peek(11) == 0x199;
      assert s21.Peek(12) == 0x16a;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s28, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 156
    * Starting at 0x11c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x199

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x199;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap6(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap5(s3);
      var s5 := Swap1(s4);
      var s6 := Swap5(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Swap5(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x199;
      assert s11.Peek(5) == 0x16a;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s14, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 38
    * Starting at 0x199
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x199 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0449);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s3, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 63
    * Starting at 0x449
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x449 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0487);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x02b6);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x2b6;
      assert s11.Peek(4) == 0x487;
      assert s11.Peek(7) == 0x16a;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s21, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 53
    * Starting at 0x2b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x487

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x487;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0x487;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0cf3);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s21, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 108
    * Starting at 0xcf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x487

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x487;
      assert s1.Peek(4) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x487;
      assert s11.Peek(9) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x487;
      assert s21.Peek(7) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x487;
      assert s31.Peek(12) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0d67);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s41, gas - 1)
      else
        ExecuteFromCFGNode_s175(s41, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 109
    * Starting at 0xd5e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x487

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x487;
      assert s1.Peek(10) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 176
    * Segment Id for this node is: 110
    * Starting at 0xd67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x487

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x487;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(6) == 0x487;
      assert s11.Peek(9) == 0x16a;
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
      assert s21.Peek(5) == 0x487;
      assert s21.Peek(8) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12af);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s28, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 175
    * Starting at 0x12af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x487

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x487;
      assert s1.Peek(8) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s10, gas - 1)
      else
        ExecuteFromCFGNode_s178(s10, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 176
    * Starting at 0x12bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x487

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x487;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 179
    * Segment Id for this node is: 177
    * Starting at 0x12c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x487

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x487;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x112c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s7, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 141
    * Starting at 0x112c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x487

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x487;
      assert s1.Peek(12) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s8, gas - 1)
      else
        ExecuteFromCFGNode_s181(s8, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 142
    * Starting at 0x1136
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x487

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x487;
      assert s1.Peek(13) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 182
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x487

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x487;
      assert s1.Peek(12) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s3, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x487

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x487;
      assert s1.Peek(10) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s7, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x487

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x487;
      assert s1.Peek(6) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 64
    * Starting at 0x487
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x487 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0584);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s4, gas - 1)
      else
        ExecuteFromCFGNode_s186(s4, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 65
    * Starting at 0x48d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x04e1);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x4e1;
      assert s11.Peek(5) == 0x16a;
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push32(s17, 0x726f636b657444414f50726f746f636f6c50726f706f73616c73000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x4e1;
      assert s21.Peek(5) == 0x16a;
      var s22 := Push2(s21, 0x0d8b);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s23, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 111
    * Starting at 0xd8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x4e1

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e1;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0da2);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x027b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x27b;
      assert s11.Peek(3) == 0xda2;
      assert s11.Peek(7) == 0x4e1;
      assert s11.Peek(11) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x12cc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s14, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 178
    * Starting at 0x12cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x27b

    requires s0.stack[3] == 0xda2

    requires s0.stack[7] == 0x4e1

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x27b;
      assert s1.Peek(3) == 0xda2;
      assert s1.Peek(7) == 0x4e1;
      assert s1.Peek(11) == 0x16a;
      var s2 := Push32(s1, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x128b);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x128b;
      assert s11.Peek(7) == 0x27b;
      assert s11.Peek(8) == 0xda2;
      assert s11.Peek(12) == 0x4e1;
      assert s11.Peek(16) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s12, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x128b

    requires s0.stack[6] == 0x27b

    requires s0.stack[7] == 0xda2

    requires s0.stack[11] == 0x4e1

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(6) == 0x27b;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x4e1;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0x4e1

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x27b;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0x4e1;
      assert s1.Peek(18) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s7, gas - 1)
      else
        ExecuteFromCFGNode_s191(s7, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0x4e1

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x128b;
      assert s1.Peek(10) == 0x27b;
      assert s1.Peek(11) == 0xda2;
      assert s1.Peek(15) == 0x4e1;
      assert s1.Peek(19) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x128b;
      assert s11.Peek(10) == 0x27b;
      assert s11.Peek(11) == 0xda2;
      assert s11.Peek(15) == 0x4e1;
      assert s11.Peek(19) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s14, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0x4e1

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x27b;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0x4e1;
      assert s1.Peek(18) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x128b;
      assert s11.Peek(6) == 0x27b;
      assert s11.Peek(7) == 0xda2;
      assert s11.Peek(11) == 0x4e1;
      assert s11.Peek(15) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s14, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x27b

    requires s0.stack[5] == 0xda2

    requires s0.stack[9] == 0x4e1

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x27b;
      assert s1.Peek(5) == 0xda2;
      assert s1.Peek(9) == 0x4e1;
      assert s1.Peek(13) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s7, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 50
    * Starting at 0x27b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xda2

    requires s0.stack[5] == 0x4e1

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda2;
      assert s1.Peek(5) == 0x4e1;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(2) == 0xda2;
      assert s11.Peek(6) == 0x4e1;
      assert s11.Peek(10) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0c5b);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s21, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 105
    * Starting at 0xc5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xda2

    requires s0.stack[5] == 0x4e1

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda2;
      assert s1.Peek(5) == 0x4e1;
      assert s1.Peek(9) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xda2;
      assert s11.Peek(10) == 0x4e1;
      assert s11.Peek(14) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0xda2;
      assert s21.Peek(8) == 0x4e1;
      assert s21.Peek(12) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0xda2;
      assert s31.Peek(13) == 0x4e1;
      assert s31.Peek(17) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0ccf);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s41, gas - 1)
      else
        ExecuteFromCFGNode_s196(s41, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 106
    * Starting at 0xcc6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x4e1

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x4e1;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 197
    * Segment Id for this node is: 107
    * Starting at 0xccf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x4e1

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xda2;
      assert s1.Peek(10) == 0x4e1;
      assert s1.Peek(14) == 0x16a;
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
      assert s11.Peek(6) == 0xda2;
      assert s11.Peek(10) == 0x4e1;
      assert s11.Peek(14) == 0x16a;
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
      assert s21.Peek(5) == 0xda2;
      assert s21.Peek(9) == 0x4e1;
      assert s21.Peek(13) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1292);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s28, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 172
    * Starting at 0x1292
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0xda2

    requires s0.stack[9] == 0x4e1

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0xda2;
      assert s1.Peek(9) == 0x4e1;
      assert s1.Peek(13) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12a4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s10, gas - 1)
      else
        ExecuteFromCFGNode_s199(s10, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 173
    * Starting at 0x12a0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x4e1

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x4e1;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 200
    * Segment Id for this node is: 174
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x4e1

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0xda2;
      assert s1.Peek(10) == 0x4e1;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x11d4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s7, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 157
    * Starting at 0x11d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0x4e1

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xda2;
      assert s1.Peek(13) == 0x4e1;
      assert s1.Peek(17) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s8, gas - 1)
      else
        ExecuteFromCFGNode_s202(s8, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 158
    * Starting at 0x11f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0x4e1

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0x4e1;
      assert s1.Peek(18) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 203
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0x4e1

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xda2;
      assert s1.Peek(13) == 0x4e1;
      assert s1.Peek(17) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s3, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0xda2

    requires s0.stack[11] == 0x4e1

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x4e1;
      assert s1.Peek(15) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s7, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xda2

    requires s0.stack[7] == 0x4e1

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xda2;
      assert s1.Peek(7) == 0x4e1;
      assert s1.Peek(11) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s6, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 112
    * Starting at 0xda2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4e1

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4e1;
      assert s1.Peek(8) == 0x16a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x0296);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s8, gas - 1)
      else
        ExecuteFromCFGNode_s207(s8, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 113
    * Starting at 0xdc0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4e1

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x4e1;
      assert s1.Peek(8) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x12);
      assert s11.Peek(5) == 0x4e1;
      assert s11.Peek(9) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x4e1;
      assert s21.Peek(9) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s24, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 59
    * Starting at 0x408
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x4e1

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4e1;
      assert s1.Peek(8) == 0x16a;
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

  /** Node 209
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4e1

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4e1;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s6, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 66
    * Starting at 0x4e1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0584);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s6, gas - 1)
      else
        ExecuteFromCFGNode_s211(s6, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 67
    * Starting at 0x4fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x39);
      assert s11.Peek(4) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f6e6c792044414f2050726f746f636f6c2050726f706f73616c7320636f6e74);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x726163742063616e2075706461746520612073657474696e6700000000000000);
      assert s21.Peek(4) == 0x16a;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x0408);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s29, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 68
    * Starting at 0x584
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x584 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x05c2);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x02b6);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x2b6;
      assert s11.Peek(4) == 0x5c2;
      assert s11.Peek(7) == 0x16a;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s21, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 53
    * Starting at 0x2b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x5c2

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5c2;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0x5c2;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0cf3);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s21, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 108
    * Starting at 0xcf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x5c2

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5c2;
      assert s1.Peek(4) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x5c2;
      assert s11.Peek(9) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x5c2;
      assert s21.Peek(7) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x5c2;
      assert s31.Peek(12) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0d67);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s41, gas - 1)
      else
        ExecuteFromCFGNode_s215(s41, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 109
    * Starting at 0xd5e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x5c2

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 216
    * Segment Id for this node is: 110
    * Starting at 0xd67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x5c2

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5c2;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(6) == 0x5c2;
      assert s11.Peek(9) == 0x16a;
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
      assert s21.Peek(5) == 0x5c2;
      assert s21.Peek(8) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12af);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s28, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 175
    * Starting at 0x12af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x5c2

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x5c2;
      assert s1.Peek(8) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s219(s10, gas - 1)
      else
        ExecuteFromCFGNode_s218(s10, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 176
    * Starting at 0x12bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x5c2

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 219
    * Segment Id for this node is: 177
    * Starting at 0x12c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x5c2

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x5c2;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x112c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s7, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 141
    * Starting at 0x112c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s8, gas - 1)
      else
        ExecuteFromCFGNode_s221(s8, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 142
    * Starting at 0x1136
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x5c2;
      assert s1.Peek(13) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 222
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s3, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x16a;
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
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x5c2

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5c2;
      assert s1.Peek(6) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s6, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 69
    * Starting at 0x5c2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x09c7);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s4, gas - 1)
      else
        ExecuteFromCFGNode_s226(s4, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 70
    * Starting at 0x5c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x05da);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x127f);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s11, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 170
    * Starting at 0x127f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x5da

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5da;
      assert s1.Peek(6) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x128b);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x123d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s7, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x128b

    requires s0.stack[6] == 0x5da

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(6) == 0x5da;
      assert s1.Peek(10) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s229(s5, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x5da

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x5da;
      assert s1.Peek(13) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s7, gas - 1)
      else
        ExecuteFromCFGNode_s230(s7, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x5da

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x128b;
      assert s1.Peek(10) == 0x5da;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x128b;
      assert s11.Peek(10) == 0x5da;
      assert s11.Peek(14) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s14, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x5da

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x5da;
      assert s1.Peek(13) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x128b;
      assert s11.Peek(6) == 0x5da;
      assert s11.Peek(10) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s14, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x5da

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5da;
      assert s1.Peek(8) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s7, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 71
    * Starting at 0x5da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(3) == 0x16a;
      var s22 := Push1(s21, 0x40);
      var s23 := MLoad(s22);
      var s24 := Push1(s23, 0x20);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0625);
      var s27 := Swap1(s26);
      var s28 := Push32(s27, 0x6d656d626572732e71756f72756d000000000000000000000000000000000000);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x0e);
      assert s31.Peek(2) == 0x625;
      assert s31.Peek(6) == 0x16a;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s34, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 72
    * Starting at 0x625
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x625 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup2(s19);
      var s21 := Sub(s20);
      assert s21.Peek(4) == 0x16a;
      var s22 := Push2(s21, 0x06f2);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s23, gas - 1)
      else
        ExecuteFromCFGNode_s235(s23, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 73
    * Starting at 0x642
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x642 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0x0713e24c43730000);
      assert s1.Peek(4) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0661);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s237(s8, gas - 1)
      else
        ExecuteFromCFGNode_s236(s8, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 74
    * Starting at 0x654
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x654 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push8(s1, 0x0a688906bd8b0000);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s237(s5, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 75
    * Starting at 0x661
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x661 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
      var s2 := Push2(s1, 0x06ed);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s3, gas - 1)
      else
        ExecuteFromCFGNode_s238(s3, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 76
    * Starting at 0x666
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x666 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x26);
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x51756f72756d2073657474696e67206d757374206265203e3d20353125202620);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x3c3d203735250000000000000000000000000000000000000000000000000000);
      assert s21.Peek(5) == 0x16a;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x0408);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s29, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 59
    * Starting at 0x408
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
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

  /** Node 240
    * Segment Id for this node is: 77
    * Starting at 0x6ed
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push2(s1, 0x09c5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s3, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 90
    * Starting at 0x9c5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s242(s2, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 91
    * Starting at 0x9c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0445);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x09df);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0x9df;
      assert s11.Peek(4) == 0x445;
      assert s11.Peek(7) == 0x16a;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x126d);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s15, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x9df

    requires s0.stack[4] == 0x445

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9df;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0x9df;
      assert s11.Peek(9) == 0x445;
      assert s11.Peek(12) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s12, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x9df

    requires s0.stack[8] == 0x445

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x9df;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(11) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s245(s5, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x9df

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x9df;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s7, gas - 1)
      else
        ExecuteFromCFGNode_s246(s7, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x9df

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x9df;
      assert s1.Peek(12) == 0x445;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0x9df;
      assert s11.Peek(12) == 0x445;
      assert s11.Peek(15) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s14, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x9df

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x9df;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(14) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0x9df;
      assert s11.Peek(8) == 0x445;
      assert s11.Peek(11) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s14, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x9df

    requires s0.stack[6] == 0x445

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x9df;
      assert s1.Peek(6) == 0x445;
      assert s1.Peek(9) == 0x16a;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s8, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 92
    * Starting at 0x9df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x445

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x445;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0x445;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup3(s19);
      var s21 := Push2(s20, 0x0eb6);
      assert s21.Peek(0) == 0xeb6;
      assert s21.Peek(3) == 0x445;
      assert s21.Peek(6) == 0x16a;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s22, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 120
    * Starting at 0xeb6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x445

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x445;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xe2a4853a00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x445;
      assert s11.Peek(8) == 0x16a;
      var s12 := Dup5(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup4(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Push2(s20, 0x0100);
      assert s21.Peek(5) == 0x445;
      assert s21.Peek(8) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Div(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Swap1(s26);
      var s28 := Push4(s27, 0xe2a4853a);
      var s29 := Swap1(s28);
      var s30 := Push1(s29, 0x44);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x445;
      assert s31.Peek(8) == 0x16a;
      var s32 := Push2(s31, 0x0e80);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s33, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 78
    * Starting at 0x6f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x6d656d626572732e6c656176652e74696d650000000000000000000000000000);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x32);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x16a;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup4(s14);
      var s16 := Sub(s15);
      var s17 := Sub(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(6) == 0x16a;
      var s22 := MStore(s21);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Keccak256(s27);
      var s29 := Dup2(s28);
      var s30 := Sub(s29);
      var s31 := Push2(s30, 0x07a6);
      assert s31.Peek(0) == 0x7a6;
      assert s31.Peek(5) == 0x16a;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s254(s32, gas - 1)
      else
        ExecuteFromCFGNode_s252(s32, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 79
    * Starting at 0x73b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push3(s0, 0x127500);
      assert s1.Peek(4) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x06ed);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s5, gas - 1)
      else
        ExecuteFromCFGNode_s253(s5, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 80
    * Starting at 0x745
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x745 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x17);
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x56616c7565206d757374206265203c2031342064617973000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s24, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 81
    * Starting at 0x7a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x70726f706f73616c2e766f74652e74696d650000000000000000000000000000);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x32);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x16a;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup4(s14);
      var s16 := Sub(s15);
      var s17 := Sub(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(6) == 0x16a;
      var s22 := MStore(s21);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Keccak256(s27);
      var s29 := Dup2(s28);
      var s30 := Sub(s29);
      var s31 := Push2(s30, 0x085b);
      assert s31.Peek(0) == 0x85b;
      assert s31.Peek(5) == 0x16a;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s32, gas - 1)
      else
        ExecuteFromCFGNode_s255(s32, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 82
    * Starting at 0x7ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push3(s0, 0x015180);
      assert s1.Peek(4) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x06ed);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s6, gas - 1)
      else
        ExecuteFromCFGNode_s256(s6, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 83
    * Starting at 0x7fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x16);
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x56616c7565206d757374206265203e3d20312064617900000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s24, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 84
    * Starting at 0x85b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x70726f706f73616c2e657865637574652e74696d650000000000000000000000);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x35);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x16a;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup4(s14);
      var s16 := Sub(s15);
      var s17 := Sub(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(6) == 0x16a;
      var s22 := MStore(s21);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Keccak256(s27);
      var s29 := Dup2(s28);
      var s30 := Sub(s29);
      var s31 := Push2(s30, 0x0910);
      assert s31.Peek(0) == 0x910;
      assert s31.Peek(5) == 0x16a;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s32, gas - 1)
      else
        ExecuteFromCFGNode_s258(s32, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 85
    * Starting at 0x8a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push3(s0, 0x015180);
      assert s1.Peek(4) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x06ed);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s6, gas - 1)
      else
        ExecuteFromCFGNode_s259(s6, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 86
    * Starting at 0x8af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x16);
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x56616c7565206d757374206265203e3d20312064617900000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s24, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 87
    * Starting at 0x910
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x910 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x70726f706f73616c2e616374696f6e2e74696d65000000000000000000000000);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x34);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x16a;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup4(s14);
      var s16 := Sub(s15);
      var s17 := Sub(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(6) == 0x16a;
      var s22 := MStore(s21);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Keccak256(s27);
      var s29 := Dup2(s28);
      var s30 := Sub(s29);
      var s31 := Push2(s30, 0x09c5);
      assert s31.Peek(0) == 0x9c5;
      assert s31.Peek(5) == 0x16a;
      var s32 := JumpI(s31);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s31.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s32, gas - 1)
      else
        ExecuteFromCFGNode_s261(s32, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 88
    * Starting at 0x959
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x959 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push3(s0, 0x015180);
      assert s1.Peek(4) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x09c5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s6, gas - 1)
      else
        ExecuteFromCFGNode_s262(s6, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 89
    * Starting at 0x964
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x964 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x16);
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x56616c7565206d757374206265203e3d20312064617900000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s24, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 13
    * Starting at 0x81
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x1bfcc24e);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00b2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s383(s6, gas - 1)
      else
        ExecuteFromCFGNode_s264(s6, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 14
    * Starting at 0x8d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1bfcc24e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0134);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s5, gas - 1)
      else
        ExecuteFromCFGNode_s265(s5, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 15
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x2a57d018);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0157);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s5, gas - 1)
      else
        ExecuteFromCFGNode_s266(s5, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x54fd4d50);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x016c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s5, gas - 1)
      else
        ExecuteFromCFGNode_s267(s5, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
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

  /** Node 268
    * Segment Id for this node is: 35
    * Starting at 0x16c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0179);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s9, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 36
    * Starting at 0x179
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x179

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x179;
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
      assert s11.Peek(1) == 0x179;
      var s12 := Push2(s11, 0x00eb);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s13, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 24
    * Starting at 0xeb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x179

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x179;
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
    * Segment Id for this node is: 32
    * Starting at 0x157
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x016a);
      var s3 := Push2(s2, 0x0165);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x113d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s7, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 144
    * Starting at 0x113d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x165

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x165;
      assert s1.Peek(3) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x1150);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s11, gas - 1)
      else
        ExecuteFromCFGNode_s273(s11, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 145
    * Starting at 0x114c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x165

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x165;
      assert s1.Peek(6) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 274
    * Segment Id for this node is: 146
    * Starting at 0x1150
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x165

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x165;
      assert s1.Peek(5) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1167);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s276(s9, gas - 1)
      else
        ExecuteFromCFGNode_s275(s9, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 147
    * Starting at 0x1163
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1163 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x165

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x165;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 276
    * Segment Id for this node is: 148
    * Starting at 0x1167
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1167 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x165

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x165;
      assert s1.Peek(6) == 0x16a;
      var s2 := Push2(s1, 0x1173);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s8, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 126
    * Starting at 0x1044
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1173

    requires s0.stack[8] == 0x165

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1173;
      assert s1.Peek(8) == 0x165;
      assert s1.Peek(9) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x1055);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s279(s9, gas - 1)
      else
        ExecuteFromCFGNode_s278(s9, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 127
    * Starting at 0x1051
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1173

    requires s0.stack[9] == 0x165

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1173;
      assert s1.Peek(10) == 0x165;
      assert s1.Peek(11) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 279
    * Segment Id for this node is: 128
    * Starting at 0x1055
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1173

    requires s0.stack[9] == 0x165

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1173;
      assert s1.Peek(9) == 0x165;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1070);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s10, gas - 1)
      else
        ExecuteFromCFGNode_s280(s10, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 129
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1173

    requires s0.stack[11] == 0x165

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1070);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1173;
      assert s1.Peek(12) == 0x165;
      assert s1.Peek(13) == 0x16a;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s3, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1070

    requires s0.stack[6] == 0x1173

    requires s0.stack[12] == 0x165

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1173;
      assert s1.Peek(12) == 0x165;
      assert s1.Peek(13) == 0x16a;
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

  /** Node 282
    * Segment Id for this node is: 130
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1173

    requires s0.stack[11] == 0x165

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1173;
      assert s1.Peek(11) == 0x165;
      assert s1.Peek(12) == 0x16a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x1173;
      assert s11.Peek(15) == 0x165;
      assert s11.Peek(16) == 0x16a;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x1173;
      assert s21.Peek(16) == 0x165;
      assert s21.Peek(17) == 0x16a;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x10b6);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s26, gas - 1)
      else
        ExecuteFromCFGNode_s283(s26, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 131
    * Starting at 0x10af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1173

    requires s0.stack[13] == 0x165

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10b6);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1173;
      assert s1.Peek(14) == 0x165;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s3, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x10b6

    requires s0.stack[8] == 0x1173

    requires s0.stack[14] == 0x165

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1173;
      assert s1.Peek(14) == 0x165;
      assert s1.Peek(15) == 0x16a;
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

  /** Node 285
    * Segment Id for this node is: 132
    * Starting at 0x10b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1173

    requires s0.stack[13] == 0x165

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1173;
      assert s1.Peek(13) == 0x165;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1173;
      assert s11.Peek(17) == 0x165;
      assert s11.Peek(18) == 0x16a;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s17, gas - 1)
      else
        ExecuteFromCFGNode_s286(s17, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 133
    * Starting at 0x10cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1173

    requires s0.stack[13] == 0x165

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1173;
      assert s1.Peek(14) == 0x165;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 287
    * Segment Id for this node is: 134
    * Starting at 0x10cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1173

    requires s0.stack[13] == 0x165

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1173;
      assert s1.Peek(13) == 0x165;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x1173;
      assert s11.Peek(15) == 0x165;
      assert s11.Peek(16) == 0x16a;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1173;
      assert s21.Peek(11) == 0x165;
      assert s21.Peek(12) == 0x16a;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s28, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 149
    * Starting at 0x1173
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1173 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x165

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x165;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push2(s8, 0x1184);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x112c);
      assert s11.Peek(0) == 0x112c;
      assert s11.Peek(2) == 0x1184;
      assert s11.Peek(8) == 0x165;
      assert s11.Peek(9) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s12, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 141
    * Starting at 0x112c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1184

    requires s0.stack[7] == 0x165

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1184;
      assert s1.Peek(7) == 0x165;
      assert s1.Peek(8) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s8, gas - 1)
      else
        ExecuteFromCFGNode_s290(s8, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 142
    * Starting at 0x1136
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1184

    requires s0.stack[7] == 0x165

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1184;
      assert s1.Peek(8) == 0x165;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 291
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1184

    requires s0.stack[7] == 0x165

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1184;
      assert s1.Peek(7) == 0x165;
      assert s1.Peek(8) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s3, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 150
    * Starting at 0x1184
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1184 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x165

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x165;
      assert s1.Peek(6) == 0x16a;
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
      ExecuteFromCFGNode_s293(s11, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 33
    * Starting at 0x165
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x165 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x02d1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s294(s3, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 54
    * Starting at 0x2d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x030f);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x02b6);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x2b6;
      assert s11.Peek(4) == 0x30f;
      assert s11.Peek(7) == 0x16a;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s21, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 53
    * Starting at 0x2b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x30f

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x30f;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0x30f;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0cf3);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s21, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 108
    * Starting at 0xcf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x30f

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x30f;
      assert s1.Peek(4) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x30f;
      assert s11.Peek(9) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x30f;
      assert s21.Peek(7) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x30f;
      assert s31.Peek(12) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0d67);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s298(s41, gas - 1)
      else
        ExecuteFromCFGNode_s297(s41, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 109
    * Starting at 0xd5e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x30f

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x30f;
      assert s1.Peek(10) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 298
    * Segment Id for this node is: 110
    * Starting at 0xd67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x30f

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x30f;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(6) == 0x30f;
      assert s11.Peek(9) == 0x16a;
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
      assert s21.Peek(5) == 0x30f;
      assert s21.Peek(8) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12af);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s28, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 175
    * Starting at 0x12af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x30f

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x30f;
      assert s1.Peek(8) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s10, gas - 1)
      else
        ExecuteFromCFGNode_s300(s10, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 176
    * Starting at 0x12bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x30f

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x30f;
      assert s1.Peek(10) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 301
    * Segment Id for this node is: 177
    * Starting at 0x12c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x30f

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x30f;
      assert s1.Peek(9) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x112c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s7, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 141
    * Starting at 0x112c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x30f

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x30f;
      assert s1.Peek(12) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s304(s8, gas - 1)
      else
        ExecuteFromCFGNode_s303(s8, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 142
    * Starting at 0x1136
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x30f

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x30f;
      assert s1.Peek(13) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 304
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x30f

    requires s0.stack[12] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x30f;
      assert s1.Peek(12) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s305(s3, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x30f

    requires s0.stack[10] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x30f;
      assert s1.Peek(10) == 0x16a;
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
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x30f

    requires s0.stack[6] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x30f;
      assert s1.Peek(6) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s6, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 55
    * Starting at 0x30f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0411);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s4, gas - 1)
      else
        ExecuteFromCFGNode_s308(s4, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 56
    * Starting at 0x315
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x315 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0369);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x369;
      assert s11.Peek(5) == 0x16a;
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push32(s17, 0x726f636b657444414f50726f746f636f6c50726f706f73616c73000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x369;
      assert s21.Peek(5) == 0x16a;
      var s22 := Push2(s21, 0x0d8b);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s23, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 111
    * Starting at 0xd8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x369

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x369;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0da2);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x027b);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x27b;
      assert s11.Peek(3) == 0xda2;
      assert s11.Peek(7) == 0x369;
      assert s11.Peek(11) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x12cc);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s14, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 178
    * Starting at 0x12cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x27b

    requires s0.stack[3] == 0xda2

    requires s0.stack[7] == 0x369

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x27b;
      assert s1.Peek(3) == 0xda2;
      assert s1.Peek(7) == 0x369;
      assert s1.Peek(11) == 0x16a;
      var s2 := Push32(s1, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x128b);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x128b;
      assert s11.Peek(7) == 0x27b;
      assert s11.Peek(8) == 0xda2;
      assert s11.Peek(12) == 0x369;
      assert s11.Peek(16) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s12, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x128b

    requires s0.stack[6] == 0x27b

    requires s0.stack[7] == 0xda2

    requires s0.stack[11] == 0x369

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(6) == 0x27b;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x369;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s312(s5, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0x369

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x27b;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0x369;
      assert s1.Peek(18) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s314(s7, gas - 1)
      else
        ExecuteFromCFGNode_s313(s7, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0x369

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x128b;
      assert s1.Peek(10) == 0x27b;
      assert s1.Peek(11) == 0xda2;
      assert s1.Peek(15) == 0x369;
      assert s1.Peek(19) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x128b;
      assert s11.Peek(10) == 0x27b;
      assert s11.Peek(11) == 0xda2;
      assert s11.Peek(15) == 0x369;
      assert s11.Peek(19) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s14, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x128b

    requires s0.stack[9] == 0x27b

    requires s0.stack[10] == 0xda2

    requires s0.stack[14] == 0x369

    requires s0.stack[18] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x128b;
      assert s1.Peek(9) == 0x27b;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0x369;
      assert s1.Peek(18) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x128b;
      assert s11.Peek(6) == 0x27b;
      assert s11.Peek(7) == 0xda2;
      assert s11.Peek(11) == 0x369;
      assert s11.Peek(15) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s315(s14, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x27b

    requires s0.stack[5] == 0xda2

    requires s0.stack[9] == 0x369

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x27b;
      assert s1.Peek(5) == 0xda2;
      assert s1.Peek(9) == 0x369;
      assert s1.Peek(13) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s7, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 50
    * Starting at 0x27b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xda2

    requires s0.stack[5] == 0x369

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda2;
      assert s1.Peek(5) == 0x369;
      assert s1.Peek(9) == 0x16a;
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
      assert s11.Peek(2) == 0xda2;
      assert s11.Peek(6) == 0x369;
      assert s11.Peek(10) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0c5b);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s21, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 105
    * Starting at 0xc5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xda2

    requires s0.stack[5] == 0x369

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xda2;
      assert s1.Peek(5) == 0x369;
      assert s1.Peek(9) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xda2;
      assert s11.Peek(10) == 0x369;
      assert s11.Peek(14) == 0x16a;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0xda2;
      assert s21.Peek(8) == 0x369;
      assert s21.Peek(12) == 0x16a;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0xda2;
      assert s31.Peek(13) == 0x369;
      assert s31.Peek(17) == 0x16a;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0ccf);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s319(s41, gas - 1)
      else
        ExecuteFromCFGNode_s318(s41, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 106
    * Starting at 0xcc6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x369

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x369;
      assert s1.Peek(15) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 319
    * Segment Id for this node is: 107
    * Starting at 0xccf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x369

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xda2;
      assert s1.Peek(10) == 0x369;
      assert s1.Peek(14) == 0x16a;
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
      assert s11.Peek(6) == 0xda2;
      assert s11.Peek(10) == 0x369;
      assert s11.Peek(14) == 0x16a;
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
      assert s21.Peek(5) == 0xda2;
      assert s21.Peek(9) == 0x369;
      assert s21.Peek(13) == 0x16a;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1292);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s28, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 172
    * Starting at 0x1292
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0xda2

    requires s0.stack[9] == 0x369

    requires s0.stack[13] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0xda2;
      assert s1.Peek(9) == 0x369;
      assert s1.Peek(13) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12a4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s10, gas - 1)
      else
        ExecuteFromCFGNode_s321(s10, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 173
    * Starting at 0x12a0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x369

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x369;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 322
    * Segment Id for this node is: 174
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0xda2

    requires s0.stack[10] == 0x369

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0xda2;
      assert s1.Peek(10) == 0x369;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x11d4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s7, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 157
    * Starting at 0x11d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0x369

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xda2;
      assert s1.Peek(13) == 0x369;
      assert s1.Peek(17) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s325(s8, gas - 1)
      else
        ExecuteFromCFGNode_s324(s8, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 158
    * Starting at 0x11f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0x369

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0xda2;
      assert s1.Peek(14) == 0x369;
      assert s1.Peek(18) == 0x16a;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 325
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0xda2

    requires s0.stack[13] == 0x369

    requires s0.stack[17] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0xda2;
      assert s1.Peek(13) == 0x369;
      assert s1.Peek(17) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s3, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0xda2

    requires s0.stack[11] == 0x369

    requires s0.stack[15] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0xda2;
      assert s1.Peek(11) == 0x369;
      assert s1.Peek(15) == 0x16a;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s327(s7, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xda2

    requires s0.stack[7] == 0x369

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xda2;
      assert s1.Peek(7) == 0x369;
      assert s1.Peek(11) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s6, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 112
    * Starting at 0xda2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x369

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x369;
      assert s1.Peek(8) == 0x16a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x0296);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s331(s8, gas - 1)
      else
        ExecuteFromCFGNode_s329(s8, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 113
    * Starting at 0xdc0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x369

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x369;
      assert s1.Peek(8) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x12);
      assert s11.Peek(5) == 0x369;
      assert s11.Peek(9) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x369;
      assert s21.Peek(9) == 0x16a;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0408);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s24, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 59
    * Starting at 0x408
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x369

    requires s0.stack[8] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x369;
      assert s1.Peek(8) == 0x16a;
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

  /** Node 331
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x369

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x369;
      assert s1.Peek(7) == 0x16a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s6, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 57
    * Starting at 0x369
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x369 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x16a;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0411);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s6, gas - 1)
      else
        ExecuteFromCFGNode_s333(s6, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 58
    * Starting at 0x385
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x16a;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x39);
      assert s11.Peek(4) == 0x16a;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f6e6c792044414f2050726f746f636f6c2050726f706f73616c7320636f6e74);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x726163742063616e2075706461746520612073657474696e6700000000000000);
      assert s21.Peek(4) == 0x16a;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s72(s27, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 60
    * Starting at 0x411
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16a;
      var s2 := Push2(s1, 0x0445);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0429);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0x429;
      assert s11.Peek(4) == 0x445;
      assert s11.Peek(7) == 0x16a;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x126d);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s15, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x429

    requires s0.stack[4] == 0x445

    requires s0.stack[7] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x429;
      assert s1.Peek(4) == 0x445;
      assert s1.Peek(7) == 0x16a;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0x429;
      assert s11.Peek(9) == 0x445;
      assert s11.Peek(12) == 0x16a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s12, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x429

    requires s0.stack[8] == 0x445

    requires s0.stack[11] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x429;
      assert s1.Peek(8) == 0x445;
      assert s1.Peek(11) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s337(s5, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x429

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x429;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(14) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s339(s7, gas - 1)
      else
        ExecuteFromCFGNode_s338(s7, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x429

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x429;
      assert s1.Peek(12) == 0x445;
      assert s1.Peek(15) == 0x16a;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0x429;
      assert s11.Peek(12) == 0x445;
      assert s11.Peek(15) == 0x16a;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s14, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x429

    requires s0.stack[11] == 0x445

    requires s0.stack[14] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x429;
      assert s1.Peek(11) == 0x445;
      assert s1.Peek(14) == 0x16a;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0x429;
      assert s11.Peek(8) == 0x445;
      assert s11.Peek(11) == 0x16a;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s14, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x429

    requires s0.stack[6] == 0x445

    requires s0.stack[9] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x429;
      assert s1.Peek(6) == 0x445;
      assert s1.Peek(9) == 0x16a;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s8, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 61
    * Starting at 0x429
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x429 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x445

    requires s0.stack[4] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x445;
      assert s1.Peek(4) == 0x16a;
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
      assert s11.Peek(2) == 0x445;
      assert s11.Peek(5) == 0x16a;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup3(s19);
      var s21 := Push2(s20, 0x0e21);
      assert s21.Peek(0) == 0xe21;
      assert s21.Peek(3) == 0x445;
      assert s21.Peek(6) == 0x16a;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s342(s22, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 114
    * Starting at 0xe21
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x445

    requires s0.stack[5] == 0x16a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x445;
      assert s1.Peek(5) == 0x16a;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xabfdcced00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x445;
      assert s11.Peek(8) == 0x16a;
      var s12 := Dup5(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Dup3(s14);
      var s16 := IsZero(s15);
      var s17 := IsZero(s16);
      var s18 := Push1(s17, 0x24);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0x445;
      assert s21.Peek(7) == 0x16a;
      var s22 := Push2(s21, 0x0100);
      var s23 := Swap1(s22);
      var s24 := Swap2(s23);
      var s25 := Div(s24);
      var s26 := Push20(s25, 0xffffffffffffffffffffffffffffffffffffffff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Push4(s28, 0xabfdcced);
      var s30 := Swap1(s29);
      var s31 := Push1(s30, 0x44);
      assert s31.Peek(6) == 0x445;
      assert s31.Peek(9) == 0x16a;
      var s32 := Add(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s82(s32, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 29
    * Starting at 0x134
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x134 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0147);
      var s3 := Push2(s2, 0x0142);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10ef);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s7, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 135
    * Starting at 0x10ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x142

    requires s0.stack[3] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x142;
      assert s1.Peek(3) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1101);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s10, gas - 1)
      else
        ExecuteFromCFGNode_s345(s10, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 136
    * Starting at 0x10fd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x142

    requires s0.stack[4] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x142;
      assert s1.Peek(5) == 0x147;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 346
    * Segment Id for this node is: 137
    * Starting at 0x1101
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x142

    requires s0.stack[4] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x142;
      assert s1.Peek(4) == 0x147;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1118);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s348(s9, gas - 1)
      else
        ExecuteFromCFGNode_s347(s9, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 138
    * Starting at 0x1114
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x142

    requires s0.stack[5] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x142;
      assert s1.Peek(6) == 0x147;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 348
    * Segment Id for this node is: 139
    * Starting at 0x1118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x142

    requires s0.stack[5] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x142;
      assert s1.Peek(5) == 0x147;
      var s2 := Push2(s1, 0x1124);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s349(s8, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 126
    * Starting at 0x1044
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x142

    requires s0.stack[8] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x142;
      assert s1.Peek(8) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x1055);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s351(s9, gas - 1)
      else
        ExecuteFromCFGNode_s350(s9, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 127
    * Starting at 0x1051
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1124

    requires s0.stack[8] == 0x142

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1124;
      assert s1.Peek(9) == 0x142;
      assert s1.Peek(10) == 0x147;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 351
    * Segment Id for this node is: 128
    * Starting at 0x1055
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1124

    requires s0.stack[8] == 0x142

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1124;
      assert s1.Peek(8) == 0x142;
      assert s1.Peek(9) == 0x147;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1070);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s354(s10, gas - 1)
      else
        ExecuteFromCFGNode_s352(s10, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 129
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x142

    requires s0.stack[11] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1070);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x142;
      assert s1.Peek(12) == 0x147;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s353(s3, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1070

    requires s0.stack[6] == 0x1124

    requires s0.stack[11] == 0x142

    requires s0.stack[12] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x142;
      assert s1.Peek(12) == 0x147;
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

  /** Node 354
    * Segment Id for this node is: 130
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x142

    requires s0.stack[11] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x142;
      assert s1.Peek(11) == 0x147;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x1124;
      assert s11.Peek(14) == 0x142;
      assert s11.Peek(15) == 0x147;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x1124;
      assert s21.Peek(15) == 0x142;
      assert s21.Peek(16) == 0x147;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x10b6);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s357(s26, gas - 1)
      else
        ExecuteFromCFGNode_s355(s26, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 131
    * Starting at 0x10af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x142

    requires s0.stack[13] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10b6);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x142;
      assert s1.Peek(14) == 0x147;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s3, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x10b6

    requires s0.stack[8] == 0x1124

    requires s0.stack[13] == 0x142

    requires s0.stack[14] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x142;
      assert s1.Peek(14) == 0x147;
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

  /** Node 357
    * Segment Id for this node is: 132
    * Starting at 0x10b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x142

    requires s0.stack[13] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1124;
      assert s1.Peek(12) == 0x142;
      assert s1.Peek(13) == 0x147;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1124;
      assert s11.Peek(16) == 0x142;
      assert s11.Peek(17) == 0x147;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s359(s17, gas - 1)
      else
        ExecuteFromCFGNode_s358(s17, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 133
    * Starting at 0x10cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x142

    requires s0.stack[13] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x142;
      assert s1.Peek(14) == 0x147;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 359
    * Segment Id for this node is: 134
    * Starting at 0x10cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x142

    requires s0.stack[13] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1124;
      assert s1.Peek(12) == 0x142;
      assert s1.Peek(13) == 0x147;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x1124;
      assert s11.Peek(14) == 0x142;
      assert s11.Peek(15) == 0x147;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1124;
      assert s21.Peek(10) == 0x142;
      assert s21.Peek(11) == 0x147;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s28, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x142

    requires s0.stack[6] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x142;
      assert s1.Peek(6) == 0x147;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s8, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 30
    * Starting at 0x142
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x142 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x147;
      var s2 := Push2(s1, 0x029c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s3, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 52
    * Starting at 0x29c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0296);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x02b6);
      assert s11.Peek(0) == 0x2b6;
      assert s11.Peek(4) == 0x296;
      assert s11.Peek(7) == 0x147;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x126d);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s16, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2b6

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2b6;
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x147;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0x2b6;
      assert s11.Peek(9) == 0x296;
      assert s11.Peek(12) == 0x147;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s12, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x2b6

    requires s0.stack[8] == 0x296

    requires s0.stack[11] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x2b6;
      assert s1.Peek(8) == 0x296;
      assert s1.Peek(11) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s365(s5, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x2b6

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x2b6;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0x147;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s7, gas - 1)
      else
        ExecuteFromCFGNode_s366(s7, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x2b6

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x2b6;
      assert s1.Peek(12) == 0x296;
      assert s1.Peek(15) == 0x147;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0x2b6;
      assert s11.Peek(12) == 0x296;
      assert s11.Peek(15) == 0x147;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s14, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x2b6

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x2b6;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0x147;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0x2b6;
      assert s11.Peek(8) == 0x296;
      assert s11.Peek(11) == 0x147;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s14, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2b6

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2b6;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x147;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s8, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 53
    * Starting at 0x2b6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0x147;
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
      assert s11.Peek(2) == 0x296;
      assert s11.Peek(5) == 0x147;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0cf3);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s21, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 108
    * Starting at 0xcf3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0x147;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x296;
      assert s21.Peek(7) == 0x147;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x296;
      assert s31.Peek(12) == 0x147;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0d67);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s372(s41, gas - 1)
      else
        ExecuteFromCFGNode_s371(s41, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 109
    * Starting at 0xd5e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 372
    * Segment Id for this node is: 110
    * Starting at 0xd67
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x147;
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
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0x147;
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
      assert s21.Peek(5) == 0x296;
      assert s21.Peek(8) == 0x147;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x12af);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s28, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 175
    * Starting at 0x12af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x296

    requires s0.stack[8] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x296;
      assert s1.Peek(8) == 0x147;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12c1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s375(s10, gas - 1)
      else
        ExecuteFromCFGNode_s374(s10, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 176
    * Starting at 0x12bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x147;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 375
    * Segment Id for this node is: 177
    * Starting at 0x12c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x147;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x112c);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s7, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 141
    * Starting at 0x112c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x296

    requires s0.stack[12] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x296;
      assert s1.Peek(12) == 0x147;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s378(s8, gas - 1)
      else
        ExecuteFromCFGNode_s377(s8, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 142
    * Starting at 0x1136
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1136 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x296

    requires s0.stack[12] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x296;
      assert s1.Peek(13) == 0x147;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 378
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x296

    requires s0.stack[12] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x296;
      assert s1.Peek(12) == 0x147;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s3, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x296

    requires s0.stack[10] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x147;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s7, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x147;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s6, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x147

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x147;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s6, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 31
    * Starting at 0x147
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147 as nat
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
      var s11 := Push2(s10, 0x00eb);
      assert s11.Peek(0) == 0xeb;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s12, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 18
    * Starting at 0xb2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x0a092a4e);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00d9);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s6, gas - 1)
      else
        ExecuteFromCFGNode_s384(s6, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 19
    * Starting at 0xbe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x11b5e486);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00f4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s427(s5, gas - 1)
      else
        ExecuteFromCFGNode_s385(s5, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 20
    * Starting at 0xc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1386a244);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00fc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s387(s5, gas - 1)
      else
        ExecuteFromCFGNode_s386(s5, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
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

  /** Node 387
    * Segment Id for this node is: 26
    * Starting at 0xfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x010f);
      var s3 := Push2(s2, 0x010a);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x10ef);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s388(s7, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 135
    * Starting at 0x10ef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x10a

    requires s0.stack[3] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10a;
      assert s1.Peek(3) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1101);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s390(s10, gas - 1)
      else
        ExecuteFromCFGNode_s389(s10, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 136
    * Starting at 0x10fd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x10a

    requires s0.stack[4] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x10a;
      assert s1.Peek(5) == 0x10f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 390
    * Segment Id for this node is: 137
    * Starting at 0x1101
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x10a

    requires s0.stack[4] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10a;
      assert s1.Peek(4) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1118);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s392(s9, gas - 1)
      else
        ExecuteFromCFGNode_s391(s9, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 138
    * Starting at 0x1114
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x10a

    requires s0.stack[5] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x10a;
      assert s1.Peek(6) == 0x10f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 392
    * Segment Id for this node is: 139
    * Starting at 0x1118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x10a

    requires s0.stack[5] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x10a;
      assert s1.Peek(5) == 0x10f;
      var s2 := Push2(s1, 0x1124);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x1044);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s8, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 126
    * Starting at 0x1044
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x10a

    requires s0.stack[8] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x10a;
      assert s1.Peek(8) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x1055);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s9, gas - 1)
      else
        ExecuteFromCFGNode_s394(s9, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 127
    * Starting at 0x1051
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1051 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1124

    requires s0.stack[8] == 0x10a

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1124;
      assert s1.Peek(9) == 0x10a;
      assert s1.Peek(10) == 0x10f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 395
    * Segment Id for this node is: 128
    * Starting at 0x1055
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1055 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x1124

    requires s0.stack[8] == 0x10a

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1124;
      assert s1.Peek(8) == 0x10a;
      assert s1.Peek(9) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1070);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s398(s10, gas - 1)
      else
        ExecuteFromCFGNode_s396(s10, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 129
    * Starting at 0x1069
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1069 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x10a

    requires s0.stack[11] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1070);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x10a;
      assert s1.Peek(12) == 0x10f;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s3, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1070

    requires s0.stack[6] == 0x1124

    requires s0.stack[11] == 0x10a

    requires s0.stack[12] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1070;
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x10a;
      assert s1.Peek(12) == 0x10f;
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

  /** Node 398
    * Segment Id for this node is: 130
    * Starting at 0x1070
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x10a

    requires s0.stack[11] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x10a;
      assert s1.Peek(11) == 0x10f;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x1124;
      assert s11.Peek(14) == 0x10a;
      assert s11.Peek(15) == 0x10f;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x1124;
      assert s21.Peek(15) == 0x10a;
      assert s21.Peek(16) == 0x10f;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x10b6);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s401(s26, gas - 1)
      else
        ExecuteFromCFGNode_s399(s26, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 131
    * Starting at 0x10af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x10a

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x10b6);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x10a;
      assert s1.Peek(14) == 0x10f;
      var s2 := Push2(s1, 0x1015);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s3, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 125
    * Starting at 0x1015
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x10b6

    requires s0.stack[8] == 0x1124

    requires s0.stack[13] == 0x10a

    requires s0.stack[14] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10b6;
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x10a;
      assert s1.Peek(14) == 0x10f;
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

  /** Node 401
    * Segment Id for this node is: 132
    * Starting at 0x10b6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x10a

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1124;
      assert s1.Peek(12) == 0x10a;
      assert s1.Peek(13) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1124;
      assert s11.Peek(16) == 0x10a;
      assert s11.Peek(17) == 0x10f;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10cf);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s403(s17, gas - 1)
      else
        ExecuteFromCFGNode_s402(s17, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 133
    * Starting at 0x10cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x10a

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1124;
      assert s1.Peek(13) == 0x10a;
      assert s1.Peek(14) == 0x10f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 403
    * Segment Id for this node is: 134
    * Starting at 0x10cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x1124

    requires s0.stack[12] == 0x10a

    requires s0.stack[13] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1124;
      assert s1.Peek(12) == 0x10a;
      assert s1.Peek(13) == 0x10f;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x1124;
      assert s11.Peek(14) == 0x10a;
      assert s11.Peek(15) == 0x10f;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1124;
      assert s21.Peek(10) == 0x10a;
      assert s21.Peek(11) == 0x10f;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s28, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x10a

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x10a;
      assert s1.Peek(6) == 0x10f;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s8, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 27
    * Starting at 0x10a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10f;
      var s2 := Push2(s1, 0x0261);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s3, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 49
    * Starting at 0x261
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x261 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0296);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x027b);
      assert s11.Peek(0) == 0x27b;
      assert s11.Peek(4) == 0x296;
      assert s11.Peek(7) == 0x10f;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x126d);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s16, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 169
    * Starting at 0x126d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x27b

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x27b;
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x10f;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x1124);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x123d);
      assert s11.Peek(0) == 0x123d;
      assert s11.Peek(3) == 0x1124;
      assert s11.Peek(8) == 0x27b;
      assert s11.Peek(9) == 0x296;
      assert s11.Peek(12) == 0x10f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s12, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 165
    * Starting at 0x123d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1124

    requires s0.stack[7] == 0x27b

    requires s0.stack[8] == 0x296

    requires s0.stack[11] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1124;
      assert s1.Peek(7) == 0x27b;
      assert s1.Peek(8) == 0x296;
      assert s1.Peek(11) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s409(s5, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 166
    * Starting at 0x1244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x27b

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x27b;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x125e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s411(s7, gas - 1)
      else
        ExecuteFromCFGNode_s410(s7, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 167
    * Starting at 0x124d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x27b

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x1124;
      assert s1.Peek(11) == 0x27b;
      assert s1.Peek(12) == 0x296;
      assert s1.Peek(15) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x1124;
      assert s11.Peek(11) == 0x27b;
      assert s11.Peek(12) == 0x296;
      assert s11.Peek(15) == 0x10f;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x1244);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s409(s14, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 168
    * Starting at 0x125e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x125e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1124

    requires s0.stack[10] == 0x27b

    requires s0.stack[11] == 0x296

    requires s0.stack[14] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1124;
      assert s1.Peek(10) == 0x27b;
      assert s1.Peek(11) == 0x296;
      assert s1.Peek(14) == 0x10f;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x1124;
      assert s11.Peek(7) == 0x27b;
      assert s11.Peek(8) == 0x296;
      assert s11.Peek(11) == 0x10f;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s14, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 140
    * Starting at 0x1124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x27b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x27b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x10f;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s8, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 50
    * Starting at 0x27b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0x10f;
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
      assert s11.Peek(2) == 0x296;
      assert s11.Peek(5) == 0x10f;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0c5b);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s21, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 105
    * Starting at 0xc5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x296

    requires s0.stack[4] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x296;
      assert s1.Peek(4) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0x10f;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x296;
      assert s21.Peek(7) == 0x10f;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x296;
      assert s31.Peek(12) == 0x10f;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x0ccf);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s416(s41, gas - 1)
      else
        ExecuteFromCFGNode_s415(s41, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 106
    * Starting at 0xcc6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 416
    * Segment Id for this node is: 107
    * Starting at 0xccf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xccf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x10f;
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
      assert s11.Peek(6) == 0x296;
      assert s11.Peek(9) == 0x10f;
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
      assert s21.Peek(5) == 0x296;
      assert s21.Peek(8) == 0x10f;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0296);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1292);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s28, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 172
    * Starting at 0x1292
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x296

    requires s0.stack[5] == 0x296

    requires s0.stack[8] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x296;
      assert s1.Peek(5) == 0x296;
      assert s1.Peek(8) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x12a4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s419(s10, gas - 1)
      else
        ExecuteFromCFGNode_s418(s10, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 173
    * Starting at 0x12a0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x10f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 419
    * Segment Id for this node is: 174
    * Starting at 0x12a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x128b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x11d4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s7, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 157
    * Starting at 0x11d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x296

    requires s0.stack[12] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x296;
      assert s1.Peek(12) == 0x10f;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x113a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s422(s8, gas - 1)
      else
        ExecuteFromCFGNode_s421(s8, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 158
    * Starting at 0x11f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x296

    requires s0.stack[12] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x128b;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x296;
      assert s1.Peek(13) == 0x10f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 422
    * Segment Id for this node is: 143
    * Starting at 0x113a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x128b

    requires s0.stack[6] == 0x296

    requires s0.stack[9] == 0x296

    requires s0.stack[12] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128b;
      assert s1.Peek(6) == 0x296;
      assert s1.Peek(9) == 0x296;
      assert s1.Peek(12) == 0x10f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s3, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 171
    * Starting at 0x128b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x296

    requires s0.stack[7] == 0x296

    requires s0.stack[10] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x296;
      assert s1.Peek(7) == 0x296;
      assert s1.Peek(10) == 0x10f;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s7, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x296

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x296;
      assert s1.Peek(6) == 0x10f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s6, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 51
    * Starting at 0x296
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x296 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x10f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s426(s6, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 28
    * Starting at 0x10f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      var s12 := Push2(s11, 0x00eb);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s13, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 25
    * Starting at 0xf4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e1);
      var s3 := Push2(s2, 0x0221);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s4, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 48
    * Starting at 0x221
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x221 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x021c);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(4) == 0xe1;
      var s12 := Push1(s11, 0x12);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6d656d626572732e6c656176652e74696d650000000000000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0ab7);
      assert s21.Peek(0) == 0xab7;
      assert s21.Peek(2) == 0x21c;
      assert s21.Peek(4) == 0xe1;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s22, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 22
    * Starting at 0xd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00e1);
      var s3 := Push2(s2, 0x01dc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s4, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 46
    * Starting at 0x1dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xe1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xe1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x021c);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(4) == 0xe1;
      var s12 := Push1(s11, 0x15);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x70726f706f73616c2e657865637574652e74696d650000000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0ab7);
      assert s21.Peek(0) == 0xab7;
      assert s21.Peek(2) == 0x21c;
      assert s21.Peek(4) == 0xe1;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s22, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
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
