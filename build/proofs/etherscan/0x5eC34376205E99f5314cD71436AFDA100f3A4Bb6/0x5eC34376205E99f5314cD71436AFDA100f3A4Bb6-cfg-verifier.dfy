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
      var s6 := Push2(s5, 0x007d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s7, gas - 1)
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
      var s6 := Push4(s5, 0x586fbad5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x005b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s9, gas - 1)
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
      var s2 := Push4(s1, 0x586fbad5);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0167);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s5, gas - 1)
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
      var s2 := Push4(s1, 0x6a938567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd6354e15);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01f3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s5, gas - 1)
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
      var s2 := Push4(s1, 0xeeb72866);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01fb);
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
      var s1 := Push2(s0, 0x007d);
      assert s1.Peek(0) == 0x7d;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s2, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
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
    * Segment Id for this node is: 34
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0203);
      var s3 := Push2(s2, 0x054f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s4, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 62
    * Starting at 0x54f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x203

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x203;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x1e);
      assert s11.Peek(2) == 0x203;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push32(s13, 0x537461726b576172655f4f7264657252656769737472795f323032315f310000);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s20, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 35
    * Starting at 0x203
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x203 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup4(s8);
      var s10 := MLoad(s9);
      var s11 := Dup2(s10);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup4(s14);
      var s16 := MLoad(s15);
      var s17 := Swap2(s16);
      var s18 := Swap3(s17);
      var s19 := Dup4(s18);
      var s20 := Swap3(s19);
      var s21 := Swap1(s20);
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := Swap2(s23);
      var s25 := Dup6(s24);
      var s26 := Add(s25);
      var s27 := Swap1(s26);
      var s28 := Dup1(s27);
      var s29 := Dup4(s28);
      var s30 := Dup4(s29);
      var s31 := Push1(s30, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s13(s31, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 36
    * Starting at 0x225
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x225 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x023d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s7, gas - 1)
      else
        ExecuteFromCFGNode_s14(s7, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 37
    * Starting at 0x22e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0225);
      assert s11.Peek(0) == 0x225;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s12, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 38
    * Starting at 0x23d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      var s12 := Push1(s11, 0x1f);
      var s13 := And(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x026a);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s17, gas - 1)
      else
        ExecuteFromCFGNode_s16(s17, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 39
    * Starting at 0x251
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Dup3(s1);
      var s3 := Sub(s2);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Dup4(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Sub(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := Exp(s10);
      var s12 := Sub(s11);
      var s13 := Not(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Swap2(s18);
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s17(s20, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 40
    * Starting at 0x26a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Sub(s10);
      var s12 := Swap1(s11);
      var s13 := Return(s12);
      // Segment is terminal (Revert, Stop or Return)
      s13
  }

  /** Node 18
    * Segment Id for this node is: 33
    * Starting at 0x1f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0153);
      var s3 := Push2(s2, 0x0546);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s4, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 61
    * Starting at 0x546
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x546 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x153;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 24
    * Starting at 0x153
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := MLoad(s9);
      var s11 := Swap1(s10);
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := Sub(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 21
    * Segment Id for this node is: 30
    * Starting at 0x1d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0153);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x01ec);
      assert s11.Peek(0) == 0x1ec;
      assert s11.Peek(4) == 0x153;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s12, gas - 1)
      else
        ExecuteFromCFGNode_s22(s12, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 31
    * Starting at 0x1e8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x153;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 23
    * Segment Id for this node is: 32
    * Starting at 0x1ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x153;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0535);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s5, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 59
    * Starting at 0x535
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x535 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x153;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0540);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x05ba);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s6, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 66
    * Starting at 0x5ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x540

    requires s0.stack[4] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x540;
      assert s1.Peek(4) == 0x153;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x540;
      assert s11.Peek(5) == 0x153;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0xff);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s17, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 60
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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
      ExecuteFromCFGNode_s20(s6, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 25
    * Starting at 0x167
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x167 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01c4);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0160);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x017e);
      assert s11.Peek(0) == 0x17e;
      assert s11.Peek(4) == 0x1c4;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s12, gas - 1)
      else
        ExecuteFromCFGNode_s28(s12, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 26
    * Starting at 0x17a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x1c4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 29
    * Segment Id for this node is: 27
    * Starting at 0x17e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c4;
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x1c4;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x60);
      var s17 := Dup2(s16);
      var s18 := Add(s17);
      var s19 := CallDataLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x80);
      assert s21.Peek(6) == 0x1c4;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := CallDataLoad(s23);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0xa0);
      var s27 := Dup2(s26);
      var s28 := Add(s27);
      var s29 := CallDataLoad(s28);
      var s30 := Swap1(s29);
      var s31 := Push1(s30, 0xc0);
      assert s31.Peek(8) == 0x1c4;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := CallDataLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Push1(s35, 0xe0);
      var s37 := Dup2(s36);
      var s38 := Add(s37);
      var s39 := CallDataLoad(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x0100);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s41, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 28
    * Starting at 0x1b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(11) == 0x1c4;
      var s2 := Add(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0120);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0140);
      var s11 := Add(s10);
      assert s11.Peek(11) == 0x1c4;
      var s12 := CallDataLoad(s11);
      var s13 := Push2(s12, 0x044b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s14, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 52
    * Starting at 0x44b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1c4;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Dup4(s8);
      var s10 := MStore(s9);
      var s11 := Dup14(s10);
      assert s11.Peek(15) == 0x1c4;
      var s12 := Dup3(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup15(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Dup3(s20);
      assert s21.Peek(16) == 0x1c4;
      var s22 := Dup5(s21);
      var s23 := Add(s22);
      var s24 := Dup14(s23);
      var s25 := Swap1(s24);
      var s26 := MStore(s25);
      var s27 := PushN(s26, 16, 0xffffffffffffffff0000000000000000);
      var s28 := Dup13(s27);
      var s29 := Dup6(s28);
      var s30 := Shl(s29);
      var s31 := And(s30);
      assert s31.Peek(16) == 0x1c4;
      var s32 := Push8(s31, 0xffffffffffffffff);
      var s33 := Dup13(s32);
      var s34 := Dup2(s33);
      var s35 := And(s34);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Swap2(s37);
      var s39 := Add(s38);
      var s40 := Dup6(s39);
      var s41 := Shl(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s32(s41, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 53
    * Starting at 0x48f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup12(s0);
      assert s1.Peek(18) == 0x1c4;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Add(s3);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push4(s6, 0xffffffff);
      var s8 := Dup9(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(19) == 0x1c4;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup7(s15);
      var s17 := Add(s16);
      var s18 := Dup2(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := PushN(s20, 9, 0x030000000000000000);
      assert s21.Peek(19) == 0x1c4;
      var s22 := Dup11(s21);
      var s23 := Dup5(s22);
      var s24 := And(s23);
      var s25 := Add(s24);
      var s26 := Dup8(s25);
      var s27 := Shl(s26);
      var s28 := Dup13(s27);
      var s29 := Dup5(s28);
      var s30 := And(s29);
      var s31 := Add(s30);
      assert s31.Peek(19) == 0x1c4;
      var s32 := Dup8(s31);
      var s33 := Shl(s32);
      var s34 := Swap3(s33);
      var s35 := Dup12(s34);
      var s36 := And(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s41, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 54
    * Starting at 0x4c6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[19] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Shl(s0);
      assert s1.Peek(18) == 0x1c4;
      var s2 := Swap1(s1);
      var s3 := Dup8(s2);
      var s4 := And(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Shl(s6);
      var s8 := Push1(s7, 0x80);
      var s9 := Dup6(s8);
      var s10 := Add(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(19) == 0x1c4;
      var s12 := Swap1(s11);
      var s13 := MStore(s12);
      var s14 := Swap5(s13);
      var s15 := MLoad(s14);
      var s16 := Push1(s15, 0x00);
      var s17 := Swap6(s16);
      var s18 := Swap2(s17);
      var s19 := Swap5(s18);
      var s20 := Swap2(s19);
      var s21 := Swap4(s20);
      assert s21.Peek(18) == 0x1c4;
      var s22 := Swap2(s21);
      var s23 := Swap3(s22);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Swap1(s26);
      var s28 := Dup4(s27);
      var s29 := Swap1(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(21) == 0x1c4;
      var s32 := Dup4(s31);
      var s33 := Dup11(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s33, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 55
    * Starting at 0x4ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[23] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(23) == 0x1c4;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0502);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s7, gas - 1)
      else
        ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 56
    * Starting at 0x4f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[23] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(24) == 0x1c4;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x04ea);
      assert s11.Peek(0) == 0x4ea;
      assert s11.Peek(24) == 0x1c4;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s12, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 57
    * Starting at 0x502
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 24
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -17
    * Net Capacity Effect: +17
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x502 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[23] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(23) == 0x1c4;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(15) == 0x1c4;
      var s12 := Push1(s11, 0x40);
      var s13 := MLoad(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Dup4(s15);
      var s17 := Sub(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(16) == 0x1c4;
      var s22 := Push1(s21, 0x40);
      var s23 := MStore(s22);
      var s24 := Dup1(s23);
      var s25 := MLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Keccak256(s28);
      var s30 := Swap3(s29);
      var s31 := Pop(s30);
      assert s31.Peek(14) == 0x1c4;
      var s32 := Pop(s31);
      var s33 := Pop(s32);
      var s34 := Swap(s33, 12);
      var s35 := Swap(s34, 11);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Pop(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s37(s41, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 58
    * Starting at 0x52f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x1c4;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s6, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 29
    * Starting at 0x1c4
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      var s12 := Sub(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Return(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 39
    * Segment Id for this node is: 9
    * Starting at 0x5b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x1898f47b);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0082);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s6, gas - 1)
      else
        ExecuteFromCFGNode_s40(s6, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 10
    * Starting at 0x67
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x426315ba);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00f1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s5, gas - 1)
      else
        ExecuteFromCFGNode_s41(s5, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x54351f12);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x011d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 21
    * Starting at 0x11d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0153);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0133);
      assert s11.Peek(0) == 0x133;
      assert s11.Peek(4) == 0x153;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s12, gas - 1)
      else
        ExecuteFromCFGNode_s43(s12, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 22
    * Starting at 0x12f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x153;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 44
    * Segment Id for this node is: 23
    * Starting at 0x133
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x153;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(3) == 0x153;
      var s12 := Swap2(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := CallDataLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := And(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(4) == 0x153;
      var s22 := Add(s21);
      var s23 := CallDataLoad(s22);
      var s24 := Push2(s23, 0x03e5);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s25, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 49
    * Starting at 0x3e5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x153;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(10) == 0x153;
      var s12 := Dup5(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := And(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Shl(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(12) == 0x153;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x14);
      var s24 := Add(s23);
      var s25 := Dup4(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0xa0);
      var s29 := Shl(s28);
      var s30 := Sub(s29);
      var s31 := And(s30);
      assert s31.Peek(11) == 0x153;
      var s32 := Push1(s31, 0x60);
      var s33 := Shl(s32);
      var s34 := Dup2(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x14);
      var s37 := Add(s36);
      var s38 := Dup3(s37);
      var s39 := Dup2(s38);
      var s40 := MStore(s39);
      var s41 := Push1(s40, 0x20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s46(s41, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 50
    * Starting at 0x41c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(10) == 0x153;
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(10) == 0x153;
      var s12 := Sub(s11);
      var s13 := Sub(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := MStore(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(7) == 0x153;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Keccak256(s23);
      var s25 := Swap1(s24);
      var s26 := Pop(s25);
      var s27 := Push2(s26, 0x0442);
      var s28 := Dup2(s27);
      var s29 := Push2(s28, 0x05ba);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s30, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 66
    * Starting at 0x5ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x442

    requires s0.stack[7] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x442;
      assert s1.Peek(7) == 0x153;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x442;
      assert s11.Peek(8) == 0x153;
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0xff);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s17, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 51
    * Starting at 0x442
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x153

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x153;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s9, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 18
    * Starting at 0xf1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ef);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0107);
      assert s11.Peek(0) == 0x107;
      assert s11.Peek(4) == 0xef;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s51(s12, gas - 1)
      else
        ExecuteFromCFGNode_s50(s12, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 19
    * Starting at 0x103
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xef;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 51
    * Segment Id for this node is: 20
    * Starting at 0x107
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xef;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := And(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xef;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Push2(s14, 0x033c);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s16, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 46
    * Starting at 0x33c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xef;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(9) == 0xef;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Shl(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(8) == 0xef;
      var s22 := Push1(s21, 0x14);
      var s23 := Add(s22);
      var s24 := Dup4(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x60);
      assert s31.Peek(10) == 0xef;
      var s32 := Shl(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x14);
      var s36 := Add(s35);
      var s37 := Dup3(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s53(s41, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 47
    * Starting at 0x373
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x373 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      assert s1.Peek(8) == 0xef;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Sub(s10);
      assert s11.Peek(7) == 0xef;
      var s12 := Sub(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := MStore(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(6) == 0xef;
      var s22 := Add(s21);
      var s23 := Keccak256(s22);
      var s24 := Swap1(s23);
      var s25 := Pop(s24);
      var s26 := Push2(s25, 0x0398);
      var s27 := Dup2(s26);
      var s28 := Push2(s27, 0x0586);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s29, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 63
    * Starting at 0x586
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x398

    requires s0.stack[5] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(5) == 0xef;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x398;
      assert s11.Peek(7) == 0xef;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0xff);
      var s16 := Not(s15);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Or(s20);
      assert s21.Peek(4) == 0x398;
      assert s21.Peek(8) == 0xef;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := SStore(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Push2(s27, 0x05b7);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s29, gas - 1)
      else
        ExecuteFromCFGNode_s55(s29, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 64
    * Starting at 0x5ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x398

    requires s0.stack[5] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(2) == 0x398;
      assert s1.Peek(6) == 0xef;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Or(s7);
      var s9 := Swap1(s8);
      var s10 := SStore(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s56(s10, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 65
    * Starting at 0x5b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x398

    requires s0.stack[5] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(5) == 0xef;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s3, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 48
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xef;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(7) == 0xef;
      var s12 := Sub(s11);
      var s13 := Dup6(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xef;
      var s22 := Dup5(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := MLoad(s25);
      var s27 := Push32(s26, 0x2eba3e57d193131a2cf179bbc814231639303814580222749ec25adde2cb9f38);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(6) == 0xef;
      var s32 := Push1(s31, 0x60);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Log1(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Pop(s37);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s39, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 17
    * Starting at 0xef
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
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
    * Segment Id for this node is: 13
    * Starting at 0x82
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ef);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push2(s6, 0x0180);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0099);
      assert s11.Peek(0) == 0x99;
      assert s11.Peek(4) == 0xef;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s12, gas - 1)
      else
        ExecuteFromCFGNode_s60(s12, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 14
    * Starting at 0x95
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xef;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 61
    * Segment Id for this node is: 15
    * Starting at 0x99
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xef;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := And(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xef;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup2(s12);
      var s14 := Add(s13);
      var s15 := CallDataLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := CallDataLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0xef;
      var s22 := Push1(s21, 0x60);
      var s23 := Dup2(s22);
      var s24 := Add(s23);
      var s25 := CallDataLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x80);
      var s28 := Dup2(s27);
      var s29 := Add(s28);
      var s30 := CallDataLoad(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0xef;
      var s32 := Push1(s31, 0xa0);
      var s33 := Dup2(s32);
      var s34 := Add(s33);
      var s35 := CallDataLoad(s34);
      var s36 := Swap1(s35);
      var s37 := Push1(s36, 0xc0);
      var s38 := Dup2(s37);
      var s39 := Add(s38);
      var s40 := CallDataLoad(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s41, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 16
    * Starting at 0xcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0xe0);
      assert s1.Peek(9) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Push2(s10, 0x0120);
      assert s11.Peek(11) == 0xef;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x0140);
      var s17 := Dup2(s16);
      var s18 := Add(s17);
      var s19 := CallDataLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x0160);
      assert s21.Peek(13) == 0xef;
      var s22 := Add(s21);
      var s23 := CallDataLoad(s22);
      var s24 := Push2(s23, 0x0278);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s25, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 41
    * Starting at 0x278
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 14
    * Net Stack Effect: +13
    * Net Capacity Effect: -13
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x278 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0xef;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x028d);
      var s4 := Dup13(s3);
      var s5 := Dup13(s4);
      var s6 := Dup13(s5);
      var s7 := Dup13(s6);
      var s8 := Dup13(s7);
      var s9 := Dup13(s8);
      var s10 := Dup13(s9);
      var s11 := Dup13(s10);
      assert s11.Peek(8) == 0x28d;
      assert s11.Peek(22) == 0xef;
      var s12 := Dup13(s11);
      var s13 := Dup13(s12);
      var s14 := Dup13(s13);
      var s15 := Push2(s14, 0x044b);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s16, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 52
    * Starting at 0x44b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[11] == 0x28d

    requires s0.stack[25] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x28d;
      assert s1.Peek(25) == 0xef;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Dup4(s8);
      var s10 := MStore(s9);
      var s11 := Dup14(s10);
      assert s11.Peek(15) == 0x28d;
      assert s11.Peek(29) == 0xef;
      var s12 := Dup3(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup15(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Dup3(s20);
      assert s21.Peek(16) == 0x28d;
      assert s21.Peek(30) == 0xef;
      var s22 := Dup5(s21);
      var s23 := Add(s22);
      var s24 := Dup14(s23);
      var s25 := Swap1(s24);
      var s26 := MStore(s25);
      var s27 := PushN(s26, 16, 0xffffffffffffffff0000000000000000);
      var s28 := Dup13(s27);
      var s29 := Dup6(s28);
      var s30 := Shl(s29);
      var s31 := And(s30);
      assert s31.Peek(16) == 0x28d;
      assert s31.Peek(30) == 0xef;
      var s32 := Push8(s31, 0xffffffffffffffff);
      var s33 := Dup13(s32);
      var s34 := Dup2(s33);
      var s35 := And(s34);
      var s36 := Swap2(s35);
      var s37 := Swap1(s36);
      var s38 := Swap2(s37);
      var s39 := Add(s38);
      var s40 := Dup6(s39);
      var s41 := Shl(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s41, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 53
    * Starting at 0x48f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[17] == 0x28d

    requires s0.stack[31] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup12(s0);
      assert s1.Peek(18) == 0x28d;
      assert s1.Peek(32) == 0xef;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Add(s3);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push4(s6, 0xffffffff);
      var s8 := Dup9(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(19) == 0x28d;
      assert s11.Peek(33) == 0xef;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup7(s15);
      var s17 := Add(s16);
      var s18 := Dup2(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := PushN(s20, 9, 0x030000000000000000);
      assert s21.Peek(19) == 0x28d;
      assert s21.Peek(33) == 0xef;
      var s22 := Dup11(s21);
      var s23 := Dup5(s22);
      var s24 := And(s23);
      var s25 := Add(s24);
      var s26 := Dup8(s25);
      var s27 := Shl(s26);
      var s28 := Dup13(s27);
      var s29 := Dup5(s28);
      var s30 := And(s29);
      var s31 := Add(s30);
      assert s31.Peek(19) == 0x28d;
      assert s31.Peek(33) == 0xef;
      var s32 := Dup8(s31);
      var s33 := Shl(s32);
      var s34 := Swap3(s33);
      var s35 := Dup12(s34);
      var s36 := And(s35);
      var s37 := Swap3(s36);
      var s38 := Swap1(s37);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s66(s41, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 54
    * Starting at 0x4c6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[19] == 0x28d

    requires s0.stack[33] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Shl(s0);
      assert s1.Peek(18) == 0x28d;
      assert s1.Peek(32) == 0xef;
      var s2 := Swap1(s1);
      var s3 := Dup8(s2);
      var s4 := And(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Shl(s6);
      var s8 := Push1(s7, 0x80);
      var s9 := Dup6(s8);
      var s10 := Add(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(19) == 0x28d;
      assert s11.Peek(33) == 0xef;
      var s12 := Swap1(s11);
      var s13 := MStore(s12);
      var s14 := Swap5(s13);
      var s15 := MLoad(s14);
      var s16 := Push1(s15, 0x00);
      var s17 := Swap6(s16);
      var s18 := Swap2(s17);
      var s19 := Swap5(s18);
      var s20 := Swap2(s19);
      var s21 := Swap4(s20);
      assert s21.Peek(18) == 0x28d;
      assert s21.Peek(32) == 0xef;
      var s22 := Swap2(s21);
      var s23 := Swap3(s22);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Dup2(s25);
      var s27 := Swap1(s26);
      var s28 := Dup4(s27);
      var s29 := Swap1(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(21) == 0x28d;
      assert s31.Peek(35) == 0xef;
      var s32 := Dup4(s31);
      var s33 := Dup11(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s67(s33, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 55
    * Starting at 0x4ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[23] == 0x28d

    requires s0.stack[37] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(23) == 0x28d;
      assert s1.Peek(37) == 0xef;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0502);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s7, gas - 1)
      else
        ExecuteFromCFGNode_s68(s7, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 56
    * Starting at 0x4f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[23] == 0x28d

    requires s0.stack[37] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(24) == 0x28d;
      assert s1.Peek(38) == 0xef;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x04ea);
      assert s11.Peek(0) == 0x4ea;
      assert s11.Peek(24) == 0x28d;
      assert s11.Peek(38) == 0xef;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s12, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 57
    * Starting at 0x502
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 24
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -17
    * Net Capacity Effect: +17
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x502 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[23] == 0x28d

    requires s0.stack[37] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(23) == 0x28d;
      assert s1.Peek(37) == 0xef;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(15) == 0x28d;
      assert s11.Peek(29) == 0xef;
      var s12 := Push1(s11, 0x40);
      var s13 := MLoad(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup2(s14);
      var s16 := Dup4(s15);
      var s17 := Sub(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(16) == 0x28d;
      assert s21.Peek(30) == 0xef;
      var s22 := Push1(s21, 0x40);
      var s23 := MStore(s22);
      var s24 := Dup1(s23);
      var s25 := MLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Add(s27);
      var s29 := Keccak256(s28);
      var s30 := Swap3(s29);
      var s31 := Pop(s30);
      assert s31.Peek(14) == 0x28d;
      assert s31.Peek(28) == 0xef;
      var s32 := Pop(s31);
      var s33 := Pop(s32);
      var s34 := Swap(s33, 12);
      var s35 := Swap(s34, 11);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Pop(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s70(s41, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 58
    * Starting at 0x52f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[5] == 0x28d

    requires s0.stack[20] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(4) == 0x28d;
      assert s1.Peek(19) == 0xef;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s6, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 42
    * Starting at 0x28d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0xef;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0299);
      var s5 := Dup14(s4);
      var s6 := Dup3(s5);
      var s7 := Push2(s6, 0x033c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s8, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 46
    * Starting at 0x33c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x299

    requires s0.stack[16] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x299;
      assert s1.Peek(16) == 0xef;
      var s2 := Push1(s1, 0x00);
      var s3 := Caller(s2);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(9) == 0x299;
      assert s11.Peek(23) == 0xef;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0xa0);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x60);
      var s19 := Shl(s18);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(8) == 0x299;
      assert s21.Peek(22) == 0xef;
      var s22 := Push1(s21, 0x14);
      var s23 := Add(s22);
      var s24 := Dup4(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x60);
      assert s31.Peek(10) == 0x299;
      assert s31.Peek(24) == 0xef;
      var s32 := Shl(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x14);
      var s36 := Add(s35);
      var s37 := Dup3(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s41, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 47
    * Starting at 0x373
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x373 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[8] == 0x299

    requires s0.stack[22] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      assert s1.Peek(8) == 0x299;
      assert s1.Peek(22) == 0xef;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Sub(s10);
      assert s11.Peek(7) == 0x299;
      assert s11.Peek(21) == 0xef;
      var s12 := Sub(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := MStore(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(6) == 0x299;
      assert s21.Peek(20) == 0xef;
      var s22 := Add(s21);
      var s23 := Keccak256(s22);
      var s24 := Swap1(s23);
      var s25 := Pop(s24);
      var s26 := Push2(s25, 0x0398);
      var s27 := Dup2(s26);
      var s28 := Push2(s27, 0x0586);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s29, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 63
    * Starting at 0x586
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x398

    requires s0.stack[5] == 0x299

    requires s0.stack[19] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(5) == 0x299;
      assert s1.Peek(19) == 0xef;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x398;
      assert s11.Peek(7) == 0x299;
      assert s11.Peek(21) == 0xef;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0xff);
      var s16 := Not(s15);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Or(s20);
      assert s21.Peek(4) == 0x398;
      assert s21.Peek(8) == 0x299;
      assert s21.Peek(22) == 0xef;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := SStore(s23);
      var s25 := SLoad(s24);
      var s26 := Push1(s25, 0xff);
      var s27 := And(s26);
      var s28 := Push2(s27, 0x05b7);
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s29, gas - 1)
      else
        ExecuteFromCFGNode_s75(s29, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 64
    * Starting at 0x5ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x398

    requires s0.stack[5] == 0x299

    requires s0.stack[19] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(2) == 0x398;
      assert s1.Peek(6) == 0x299;
      assert s1.Peek(20) == 0xef;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Or(s7);
      var s9 := Swap1(s8);
      var s10 := SStore(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s10, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 65
    * Starting at 0x5b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x398

    requires s0.stack[5] == 0x299

    requires s0.stack[19] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(5) == 0x299;
      assert s1.Peek(19) == 0xef;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s3, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 48
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x299

    requires s0.stack[17] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x299;
      assert s1.Peek(17) == 0xef;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(7) == 0x299;
      assert s11.Peek(21) == 0xef;
      var s12 := Sub(s11);
      var s13 := Dup6(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x299;
      assert s21.Peek(20) == 0xef;
      var s22 := Dup5(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := MLoad(s25);
      var s27 := Push32(s26, 0x2eba3e57d193131a2cf179bbc814231639303814580222749ec25adde2cb9f38);
      var s28 := Swap2(s27);
      var s29 := Dup2(s28);
      var s30 := Swap1(s29);
      var s31 := Sub(s30);
      assert s31.Peek(6) == 0x299;
      assert s31.Peek(20) == 0xef;
      var s32 := Push1(s31, 0x60);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Log1(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Pop(s37);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s39, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 43
    * Starting at 0x299
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0xef;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      assert s11.Peek(17) == 0xef;
      var s12 := Sub(s11);
      var s13 := Dup16(s12);
      var s14 := And(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup1(s18);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(16) == 0xef;
      var s22 := Dup15(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x60);
      var s26 := Dup2(s25);
      var s27 := Add(s26);
      var s28 := Dup14(s27);
      var s29 := Swap1(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x80);
      assert s31.Peek(16) == 0xef;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Dup13(s33);
      var s35 := Swap1(s34);
      var s36 := MStore(s35);
      var s37 := Push1(s36, 0xa0);
      var s38 := Dup2(s37);
      var s39 := Add(s38);
      var s40 := Dup12(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s79(s41, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 44
    * Starting at 0x2ca
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(15) == 0xef;
      var s2 := Push1(s1, 0xc0);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Dup11(s4);
      var s6 := Swap1(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0xe0);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Dup10(s10);
      assert s11.Peek(17) == 0xef;
      var s12 := Swap1(s11);
      var s13 := MStore(s12);
      var s14 := Push2(s13, 0x0100);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Dup9(s16);
      var s18 := Swap1(s17);
      var s19 := MStore(s18);
      var s20 := Push2(s19, 0x0120);
      var s21 := Dup2(s20);
      assert s21.Peek(17) == 0xef;
      var s22 := Add(s21);
      var s23 := Dup8(s22);
      var s24 := Swap1(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0140);
      var s27 := Dup2(s26);
      var s28 := Add(s27);
      var s29 := Dup7(s28);
      var s30 := Swap1(s29);
      var s31 := MStore(s30);
      assert s31.Peek(15) == 0xef;
      var s32 := Push2(s31, 0x0160);
      var s33 := Dup2(s32);
      var s34 := Add(s33);
      var s35 := Dup6(s34);
      var s36 := Swap1(s35);
      var s37 := MStore(s36);
      var s38 := Push2(s37, 0x0180);
      var s39 := Dup2(s38);
      var s40 := Add(s39);
      var s41 := Dup5(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s41, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 45
    * Starting at 0x2ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 18
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -18
    * Net Capacity Effect: +18
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[17] == 0xef

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(17) == 0xef;
      var s2 := MStore(s1);
      var s3 := Swap1(s2);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0x7f0bd0a16021c205b63f2604730537cd852ba61d30e3a7f5a1249cfcdc64ecda);
      var s6 := Swap2(s5);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := Sub(s8);
      var s10 := Push2(s9, 0x01a0);
      var s11 := Add(s10);
      assert s11.Peek(16) == 0xef;
      var s12 := Swap1(s11);
      var s13 := Log1(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0xef;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s27, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
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
