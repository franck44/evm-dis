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
      var s7 := Push2(s6, 0x00bf);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s502(s8, gas - 1)
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
      var s6 := Push4(s5, 0xa515ac67);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x007c);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s9, gas - 1)
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
      var s2 := Push4(s1, 0xba415262);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0057);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s5, gas - 1)
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
      var s2 := Push4(s1, 0xba415262);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x022e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc253a61b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0261);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdbdbd94c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0275);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf6cb7a4c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0288);
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
    * Segment Id for this node is: 59
    * Starting at 0x288
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x288 as nat
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
      var s5 := Push2(s4, 0x0293);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 60
    * Starting at 0x290
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x290 as nat
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
    * Segment Id for this node is: 61
    * Starting at 0x293
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0116);
      var s4 := Push2(s3, 0x05a5);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 91
    * Starting at 0x5a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0575);
      var s4 := Push32(s3, 0x0000000000000000000000000000000000000000000000009d70576d8e253bcf);
      var s5 := Push0(s4);
      var s6 := Push2(s5, 0x02d2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s7, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 65
    * Starting at 0x2d2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x575

    requires s0.stack[4] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := Address(s9);
      var s11 := Push1(s10, 0xc0);
      assert s11.Peek(6) == 0x575;
      assert s11.Peek(8) == 0x116;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Dup3(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Dup4(s17);
      var s19 := MLoad(s18);
      var s20 := Dup1(s19);
      var s21 := Dup5(s20);
      assert s21.Peek(9) == 0x575;
      assert s21.Peek(11) == 0x116;
      var s22 := Sub(s21);
      var s23 := Swap1(s22);
      var s24 := Swap2(s23);
      var s25 := Add(s24);
      var s26 := Dup2(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0xe0);
      var s29 := Dup4(s28);
      var s30 := Add(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(8) == 0x575;
      assert s31.Peek(10) == 0x116;
      var s32 := MStore(s31);
      var s33 := Dup3(s32);
      var s34 := MStore(s33);
      var s35 := Dup3(s34);
      var s36 := MLoad(s35);
      var s37 := PushN(s36, 9, 0x056bc75e2d63100001);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup1(s38);
      var s40 := Dup4(s39);
      var s41 := Add(s40);
      assert s41.Peek(9) == 0x575;
      assert s41.Peek(11) == 0x116;
      var s42 := Dup3(s41);
      var s43 := Swap1(s42);
      var s44 := MStore(s43);
      var s45 := Dup3(s44);
      var s46 := Dup7(s45);
      var s47 := Add(s46);
      var s48 := Dup5(s47);
      var s49 := Swap1(s48);
      var s50 := MStore(s49);
      var s51 := Dup6(s50);
      assert s51.Peek(9) == 0x575;
      assert s51.Peek(11) == 0x116;
      var s52 := MLoad(s51);
      var s53 := Dup1(s52);
      var s54 := Dup5(s53);
      var s55 := Sub(s54);
      var s56 := Dup8(s55);
      var s57 := Add(s56);
      var s58 := Dup2(s57);
      var s59 := MStore(s58);
      var s60 := Push1(s59, 0x60);
      var s61 := Swap1(s60);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s13(s61, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 66
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      var s2 := Add(s1);
      var s3 := Dup7(s2);
      var s4 := MStore(s3);
      var s5 := Dup1(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x575;
      assert s11.Peek(9) == 0x116;
      var s12 := Dup5(s11);
      var s13 := MLoad(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := Swap3(s17);
      var s19 := Dup2(s18);
      var s20 := Add(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(10) == 0x575;
      assert s21.Peek(12) == 0x116;
      var s22 := MStore(s21);
      var s23 := Swap2(s22);
      var s24 := Swap5(s23);
      var s25 := Swap1(s24);
      var s26 := Swap4(s25);
      var s27 := Dup6(s26);
      var s28 := Swap3(s27);
      var s29 := Swap1(s28);
      var s30 := Swap2(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(10) == 0x575;
      assert s31.Peek(12) == 0x116;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Dup4(s33);
      var s35 := Push2(s34, 0x036a);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s36, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 69
    * Starting at 0x36a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Dup7(s6);
      var s8 := Push2(s7, 0x037b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s9, gas - 1)
      else
        ExecuteFromCFGNode_s15(s9, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 70
    * Starting at 0x376
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x575

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Push2(s1, 0x039d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s3, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 72
    * Starting at 0x39d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x575

    requires s0.stack[11] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x575;
      assert s11.Peek(10) == 0x116;
      var s12 := Push2(s11, 0x03c5);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := Push3(s20, 0x011170);
      assert s21.Peek(3) == 0x3c5;
      assert s21.Peek(12) == 0x575;
      assert s21.Peek(14) == 0x116;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Pop(s23);
      var s25 := Push2(s24, 0x05d0);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s26, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 92
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x3c5

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Dup1(s7);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(5) == 0x3c5;
      assert s11.Peek(14) == 0x575;
      assert s11.Peek(16) == 0x116;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup5(s17);
      var s19 := Sub(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(5) == 0x3c5;
      assert s21.Peek(14) == 0x575;
      assert s21.Peek(16) == 0x116;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x44);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x3c5;
      assert s31.Peek(11) == 0x575;
      assert s31.Peek(13) == 0x116;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Dup1(s33);
      var s35 := MLoad(s34);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0x01);
      var s38 := Push1(s37, 0xe0);
      var s39 := Shl(s38);
      var s40 := Sub(s39);
      var s41 := And(s40);
      assert s41.Peek(3) == 0x3c5;
      assert s41.Peek(12) == 0x575;
      assert s41.Peek(14) == 0x116;
      var s42 := Push4(s41, 0x97a657c9);
      var s43 := Push1(s42, 0xe0);
      var s44 := Shl(s43);
      var s45 := Or(s44);
      var s46 := Swap1(s45);
      var s47 := MStore(s46);
      var s48 := Swap1(s47);
      var s49 := Jump(s48);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s49, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 73
    * Starting at 0x3c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x575

    requires s0.stack[11] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push4(s5, 0x20487ded);
      var s7 := Push1(s6, 0xe0);
      var s8 := Shl(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x575;
      assert s11.Peek(10) == 0x116;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Push32(s18, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s20 := And(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(8) == 0x575;
      assert s21.Peek(10) == 0x116;
      var s22 := Push4(s21, 0x20487ded);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0418);
      var s25 := Swap1(s24);
      var s26 := Dup10(s25);
      var s27 := Swap1(s26);
      var s28 := Dup6(s27);
      var s29 := Swap1(s28);
      var s30 := Push1(s29, 0x04);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x418;
      assert s31.Peek(12) == 0x575;
      assert s31.Peek(14) == 0x116;
      var s32 := Push2(s31, 0x0e03);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s33, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 178
    * Starting at 0xe03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x418

    requires s0.stack[12] == 0x575

    requires s0.stack[14] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x418;
      assert s11.Peek(16) == 0x575;
      assert s11.Peek(18) == 0x116;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup5(s18);
      var s20 := MLoad(s19);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(8) == 0x418;
      assert s21.Peek(17) == 0x575;
      assert s21.Peek(19) == 0x116;
      var s22 := Dup4(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0e2e);
      var s27 := Push1(s26, 0xe0);
      var s28 := Dup7(s27);
      var s29 := Add(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0dc0);
      assert s31.Peek(0) == 0xdc0;
      assert s31.Peek(3) == 0xe2e;
      assert s31.Peek(11) == 0x418;
      assert s31.Peek(20) == 0x575;
      assert s31.Peek(22) == 0x116;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s32, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xe2e

    requires s0.stack[10] == 0x418

    requires s0.stack[19] == 0x575

    requires s0.stack[21] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s21(s8, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x575

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s7, gas - 1)
      else
        ExecuteFromCFGNode_s22(s7, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x575

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe2e;
      assert s11.Peek(17) == 0x418;
      assert s11.Peek(26) == 0x575;
      assert s11.Peek(28) == 0x116;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s16, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x575

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe2e;
      assert s11.Peek(14) == 0x418;
      assert s11.Peek(23) == 0x575;
      assert s11.Peek(25) == 0x116;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe2e;
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x575;
      assert s21.Peek(23) == 0x116;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s27, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 179
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x418

    requires s0.stack[17] == 0x575

    requires s0.stack[19] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x3f);
      var s9 := Not(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(11) == 0x418;
      assert s11.Peek(20) == 0x575;
      assert s11.Peek(22) == 0x116;
      var s12 := Dup5(s11);
      var s13 := Sub(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push2(s18, 0x0e4b);
      var s20 := Dup4(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(2) == 0xe4b;
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x575;
      assert s21.Peek(23) == 0x116;
      var s22 := Push2(s21, 0x0dc0);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s23, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xe4b

    requires s0.stack[12] == 0x418

    requires s0.stack[21] == 0x575

    requires s0.stack[23] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s8, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x418

    requires s0.stack[24] == 0x575

    requires s0.stack[26] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s7, gas - 1)
      else
        ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x418

    requires s0.stack[24] == 0x575

    requires s0.stack[26] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe4b;
      assert s11.Peek(19) == 0x418;
      assert s11.Peek(28) == 0x575;
      assert s11.Peek(30) == 0x116;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s16, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x418

    requires s0.stack[24] == 0x575

    requires s0.stack[26] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe4b;
      assert s11.Peek(16) == 0x418;
      assert s11.Peek(25) == 0x575;
      assert s11.Peek(27) == 0x116;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe4b;
      assert s21.Peek(14) == 0x418;
      assert s21.Peek(23) == 0x575;
      assert s21.Peek(25) == 0x116;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s27, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 180
    * Starting at 0xe4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[10] == 0x418

    requires s0.stack[19] == 0x575

    requires s0.stack[21] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup9(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x80);
      assert s11.Peek(13) == 0x418;
      assert s11.Peek(22) == 0x575;
      assert s11.Peek(24) == 0x116;
      var s12 := Dup11(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(13) == 0x418;
      assert s21.Peek(22) == 0x575;
      assert s21.Peek(24) == 0x116;
      var s22 := Add(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Push0(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s31, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 181
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x575

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e9d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s7, gas - 1)
      else
        ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 182
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x575

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(14) == 0x418;
      assert s11.Peek(23) == 0x575;
      assert s11.Peek(25) == 0x116;
      var s12 := MStore(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Dup7(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x575;
      assert s21.Peek(23) == 0x116;
      var s22 := Add(s21);
      var s23 := Swap4(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap4(s24);
      var s26 := Swap1(s25);
      var s27 := Swap4(s26);
      var s28 := Add(s27);
      var s29 := Swap3(s28);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(12) == 0x418;
      assert s31.Peek(21) == 0x575;
      assert s31.Peek(23) == 0x116;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0e6b);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s35, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 183
    * Starting at 0xe9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x575

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup10(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(12) == 0x418;
      assert s11.Peek(21) == 0x575;
      assert s11.Peek(23) == 0x116;
      var s12 := And(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x80);
      var s18 := Dup10(s17);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup9(s20);
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x575;
      assert s21.Peek(23) == 0x116;
      var s22 := Dup3(s21);
      var s23 := Sub(s22);
      var s24 := Dup4(s23);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup11(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Swap6(s29);
      var s31 := Pop(s30);
      assert s31.Peek(10) == 0x418;
      assert s31.Peek(19) == 0x575;
      assert s31.Peek(21) == 0x116;
      var s32 := Push2(s31, 0x0ecc);
      var s33 := Dup2(s32);
      var s34 := Dup8(s33);
      var s35 := Push2(s34, 0x0dc0);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s36, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xecc

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x575

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s8, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x418

    requires s0.stack[25] == 0x575

    requires s0.stack[27] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s7, gas - 1)
      else
        ExecuteFromCFGNode_s35(s7, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x418

    requires s0.stack[25] == 0x575

    requires s0.stack[27] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xecc;
      assert s11.Peek(20) == 0x418;
      assert s11.Peek(29) == 0x575;
      assert s11.Peek(31) == 0x116;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s16, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x418

    requires s0.stack[25] == 0x575

    requires s0.stack[27] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xecc;
      assert s11.Peek(17) == 0x418;
      assert s11.Peek(26) == 0x575;
      assert s11.Peek(28) == 0x116;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xecc;
      assert s21.Peek(15) == 0x418;
      assert s21.Peek(24) == 0x575;
      assert s21.Peek(26) == 0x116;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s27, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 184
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x575

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x418;
      assert s11.Peek(12) == 0x575;
      assert s11.Peek(14) == 0x116;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s14, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 74
    * Starting at 0x418
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x575

    requires s0.stack[11] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(10) == 0x575;
      assert s11.Peek(12) == 0x116;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0433);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s16, gas - 1)
      else
        ExecuteFromCFGNode_s39(s16, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 75
    * Starting at 0x42c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 40
    * Segment Id for this node is: 76
    * Starting at 0x433
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x433 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(10) == 0x575;
      assert s11.Peek(12) == 0x116;
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
      assert s21.Peek(9) == 0x575;
      assert s21.Peek(11) == 0x116;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0457);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0eda);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s28, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 185
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x457

    requires s0.stack[9] == 0x575

    requires s0.stack[11] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0eea);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s10, gas - 1)
      else
        ExecuteFromCFGNode_s42(s10, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 186
    * Starting at 0xee7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x457

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

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

  /** Node 43
    * Segment Id for this node is: 187
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x457

    requires s0.stack[10] == 0x575

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 77
    * Starting at 0x457
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x575

    requires s0.stack[9] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap7(s1);
      var s3 := Swap6(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s10, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 89
    * Starting at 0x575
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 29
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
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
      var s9 := Push2(s8, 0x00ee);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s10, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 24
    * Starting at 0xee
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee as nat
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

  /** Node 48
    * Segment Id for this node is: 71
    * Starting at 0x37b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x575

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push32(s1, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s16(s2, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 57
    * Starting at 0x275
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x275 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0137);
      var s3 := Push2(s2, 0x0283);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d82);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s7, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 169
    * Starting at 0xd82
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x283

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0d93);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s11, gas - 1)
      else
        ExecuteFromCFGNode_s51(s11, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 170
    * Starting at 0xd90
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x283

    requires s0.stack[5] == 0x137

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

  /** Node 52
    * Segment Id for this node is: 171
    * Starting at 0xd93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x283

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0d9e);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0d6e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s7, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 167
    * Starting at 0xd6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd9e

    requires s0.stack[7] == 0x283

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x048c);
      assert s11.Peek(0) == 0x48c;
      assert s11.Peek(3) == 0xd9e;
      assert s11.Peek(9) == 0x283;
      assert s11.Peek(10) == 0x137;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s12, gas - 1)
      else
        ExecuteFromCFGNode_s54(s12, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 168
    * Starting at 0xd7f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd9e

    requires s0.stack[7] == 0x283

    requires s0.stack[8] == 0x137

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
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd9e

    requires s0.stack[7] == 0x283

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s3, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 172
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x283

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(1) == 0x283;
      assert s11.Peek(4) == 0x137;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s13, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 58
    * Starting at 0x283
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x283 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x057a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s3, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 90
    * Starting at 0x57a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0546);
      var s3 := Push32(s2, 0x000000000000000000000000000000000000000000000000383a1891ae1915b1);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x060d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s7, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 93
    * Starting at 0x60d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x546

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x23b872dd);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Caller(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x546;
      assert s11.Peek(10) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Address(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup2(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x546;
      assert s21.Peek(8) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Push32(s24, 0x000000000000000000000000ab534a239459ef03c9a389039463c7631075ecaa);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0xa0);
      var s29 := Shl(s28);
      var s30 := Sub(s29);
      var s31 := And(s30);
      assert s31.Peek(5) == 0x546;
      assert s31.Peek(8) == 0x137;
      var s32 := Swap1(s31);
      var s33 := Push4(s32, 0x23b872dd);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x64);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Dup1(s39);
      var s41 := Dup4(s40);
      assert s41.Peek(10) == 0x546;
      assert s41.Peek(13) == 0x137;
      var s42 := Sub(s41);
      var s43 := Dup2(s42);
      var s44 := Push0(s43);
      var s45 := Dup8(s44);
      var s46 := Gas(s45);
      var s47 := Call(s46);
      var s48 := IsZero(s47);
      var s49 := Dup1(s48);
      var s50 := IsZero(s49);
      var s51 := Push2(s50, 0x067d);
      assert s51.Peek(0) == 0x67d;
      assert s51.Peek(9) == 0x546;
      assert s51.Peek(12) == 0x137;
      var s52 := JumpI(s51);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s51.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s52, gas - 1)
      else
        ExecuteFromCFGNode_s60(s52, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 94
    * Starting at 0x676
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x676 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 61
    * Segment Id for this node is: 95
    * Starting at 0x67d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(7) == 0x546;
      assert s11.Peek(10) == 0x137;
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
      assert s21.Peek(6) == 0x546;
      assert s21.Peek(9) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x06a1);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1125);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s28, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 233
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x6a1

    requires s0.stack[6] == 0x546

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1135);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s10, gas - 1)
      else
        ExecuteFromCFGNode_s63(s10, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 234
    * Starting at 0x1132
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x6a1

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

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

  /** Node 64
    * Segment Id for this node is: 235
    * Starting at 0x1135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x6a1

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0cbd);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0cdf);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s7, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 151
    * Starting at 0xcdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x6a1

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x048c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s8, gas - 1)
      else
        ExecuteFromCFGNode_s66(s8, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 152
    * Starting at 0xce9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x6a1

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

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

  /** Node 67
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x6a1

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s3, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x6a1

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 96
    * Starting at 0x6a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x546

    requires s0.stack[7] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x06df);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s3, gas - 1)
      else
        ExecuteFromCFGNode_s70(s3, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 97
    * Starting at 0x6a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x546

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(6) == 0x546;
      assert s11.Peek(9) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151c985b9cd9995c8819985a5b1959);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x546;
      assert s21.Peek(9) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0501);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s28, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 83
    * Starting at 0x501
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x546

    requires s0.stack[7] == 0x137

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
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 72
    * Segment Id for this node is: 98
    * Starting at 0x6df
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x546

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Address(s10);
      assert s11.Peek(5) == 0x546;
      assert s11.Peek(8) == 0x137;
      var s12 := Push1(s11, 0xc0);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := CallValue(s15);
      var s17 := IsZero(s16);
      var s18 := Swap1(s17);
      var s19 := Push0(s18);
      var s20 := Swap1(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(7) == 0x546;
      assert s21.Peek(10) == 0x137;
      var s22 := Push1(s21, 0xe0);
      var s23 := Dup2(s22);
      var s24 := Add(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Dup2(s27);
      var s29 := Dup4(s28);
      var s30 := Sub(s29);
      var s31 := Sub(s30);
      assert s31.Peek(10) == 0x546;
      assert s31.Peek(13) == 0x137;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MStore(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Dup5(s40);
      assert s41.Peek(8) == 0x546;
      assert s41.Peek(11) == 0x137;
      var s42 := Dup7(s41);
      var s43 := Push1(s42, 0x40);
      var s44 := MLoad(s43);
      var s45 := Push1(s44, 0x20);
      var s46 := Add(s45);
      var s47 := Push2(s46, 0x0733);
      var s48 := Swap3(s47);
      var s49 := Swap2(s48);
      var s50 := Swap1(s49);
      var s51 := Swap2(s50);
      assert s51.Peek(3) == 0x733;
      assert s51.Peek(11) == 0x546;
      assert s51.Peek(14) == 0x137;
      var s52 := Dup3(s51);
      var s53 := MStore(s52);
      var s54 := Push1(s53, 0x01);
      var s55 := Push1(s54, 0x01);
      var s56 := Push1(s55, 0xa0);
      var s57 := Shl(s56);
      var s58 := Sub(s57);
      var s59 := And(s58);
      var s60 := Push1(s59, 0x20);
      var s61 := Dup3(s60);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s61, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 99
    * Starting at 0x72c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x733

    requires s0.stack[12] == 0x546

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s6, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 100
    * Starting at 0x733
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x733 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Dup2(s6);
      var s8 := Dup5(s7);
      var s9 := Sub(s8);
      var s10 := Add(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(12) == 0x546;
      assert s11.Peek(15) == 0x137;
      var s12 := MStore(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push0(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(9) == 0x546;
      assert s21.Peek(12) == 0x137;
      var s22 := MLoad(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup3(s24);
      var s26 := MStore(s25);
      var s27 := Dup1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Mul(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(10) == 0x546;
      assert s31.Peek(13) == 0x137;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := Push1(s33, 0x40);
      var s35 := MStore(s34);
      var s36 := Dup1(s35);
      var s37 := IsZero(s36);
      var s38 := Push2(s37, 0x078d);
      var s39 := JumpI(s38);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s38.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s39, gas - 1)
      else
        ExecuteFromCFGNode_s75(s39, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 101
    * Starting at 0x763
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x763 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x546

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s76(s3, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 102
    * Starting at 0x767
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x767 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push0(s10);
      assert s11.Peek(12) == 0x546;
      assert s11.Peek(15) == 0x137;
      var s12 := Dup1(s11);
      var s13 := Dup3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(11) == 0x546;
      assert s21.Peek(14) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap1(s24);
      var s26 := Sub(s25);
      var s27 := Swap1(s26);
      var s28 := Dup2(s27);
      var s29 := Push2(s28, 0x0767);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s30, gas - 1)
      else
        ExecuteFromCFGNode_s77(s30, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 103
    * Starting at 0x78b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s78(s2, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 104
    * Starting at 0x78d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x546

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x079e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s9, gas - 1)
      else
        ExecuteFromCFGNode_s79(s9, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 105
    * Starting at 0x799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Push2(s1, 0x07c0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s3, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 107
    * Starting at 0x7c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x546;
      assert s11.Peek(10) == 0x137;
      var s12 := Push2(s11, 0x07e8);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := Push3(s20, 0x011170);
      assert s21.Peek(3) == 0x7e8;
      assert s21.Peek(11) == 0x546;
      assert s21.Peek(14) == 0x137;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Pop(s23);
      var s25 := Push2(s24, 0x05d0);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s26, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 92
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x7e8

    requires s0.stack[9] == 0x546

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Dup1(s7);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(5) == 0x7e8;
      assert s11.Peek(13) == 0x546;
      assert s11.Peek(16) == 0x137;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup5(s17);
      var s19 := Sub(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(5) == 0x7e8;
      assert s21.Peek(13) == 0x546;
      assert s21.Peek(16) == 0x137;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x44);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x7e8;
      assert s31.Peek(10) == 0x546;
      assert s31.Peek(13) == 0x137;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Dup1(s33);
      var s35 := MLoad(s34);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0x01);
      var s38 := Push1(s37, 0xe0);
      var s39 := Shl(s38);
      var s40 := Sub(s39);
      var s41 := And(s40);
      assert s41.Peek(3) == 0x7e8;
      assert s41.Peek(11) == 0x546;
      assert s41.Peek(14) == 0x137;
      var s42 := Push4(s41, 0x97a657c9);
      var s43 := Push1(s42, 0xe0);
      var s44 := Shl(s43);
      var s45 := Or(s44);
      var s46 := Swap1(s45);
      var s47 := MStore(s46);
      var s48 := Swap1(s47);
      var s49 := Jump(s48);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s49, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 108
    * Starting at 0x7e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push4(s5, 0x20487ded);
      var s7 := Push1(s6, 0xe0);
      var s8 := Shl(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x546;
      assert s11.Peek(10) == 0x137;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Push0(s13);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Push32(s20, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      assert s21.Peek(9) == 0x546;
      assert s21.Peek(12) == 0x137;
      var s22 := And(s21);
      var s23 := Swap1(s22);
      var s24 := Push4(s23, 0x20487ded);
      var s25 := Swap1(s24);
      var s26 := Push2(s25, 0x083d);
      var s27 := Swap1(s26);
      var s28 := Dup10(s27);
      var s29 := Swap1(s28);
      var s30 := Dup7(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(3) == 0x83d;
      assert s31.Peek(12) == 0x546;
      assert s31.Peek(15) == 0x137;
      var s32 := Push1(s31, 0x04);
      var s33 := Add(s32);
      var s34 := Push2(s33, 0x0e03);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s35, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 178
    * Starting at 0xe03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x83d

    requires s0.stack[12] == 0x546

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x83d;
      assert s11.Peek(16) == 0x546;
      assert s11.Peek(19) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup5(s18);
      var s20 := MLoad(s19);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(8) == 0x83d;
      assert s21.Peek(17) == 0x546;
      assert s21.Peek(20) == 0x137;
      var s22 := Dup4(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0e2e);
      var s27 := Push1(s26, 0xe0);
      var s28 := Dup7(s27);
      var s29 := Add(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0dc0);
      assert s31.Peek(0) == 0xdc0;
      assert s31.Peek(3) == 0xe2e;
      assert s31.Peek(11) == 0x83d;
      assert s31.Peek(20) == 0x546;
      assert s31.Peek(23) == 0x137;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s32, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xe2e

    requires s0.stack[10] == 0x83d

    requires s0.stack[19] == 0x546

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s85(s8, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s7, gas - 1)
      else
        ExecuteFromCFGNode_s86(s7, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe2e;
      assert s11.Peek(17) == 0x83d;
      assert s11.Peek(26) == 0x546;
      assert s11.Peek(29) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s16, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe2e;
      assert s11.Peek(14) == 0x83d;
      assert s11.Peek(23) == 0x546;
      assert s11.Peek(26) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe2e;
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x546;
      assert s21.Peek(24) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s27, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 179
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x83d

    requires s0.stack[17] == 0x546

    requires s0.stack[20] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x3f);
      var s9 := Not(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(11) == 0x83d;
      assert s11.Peek(20) == 0x546;
      assert s11.Peek(23) == 0x137;
      var s12 := Dup5(s11);
      var s13 := Sub(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push2(s18, 0x0e4b);
      var s20 := Dup4(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(2) == 0xe4b;
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x546;
      assert s21.Peek(24) == 0x137;
      var s22 := Push2(s21, 0x0dc0);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s23, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xe4b

    requires s0.stack[12] == 0x83d

    requires s0.stack[21] == 0x546

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x83d

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s7, gas - 1)
      else
        ExecuteFromCFGNode_s91(s7, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x83d

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe4b;
      assert s11.Peek(19) == 0x83d;
      assert s11.Peek(28) == 0x546;
      assert s11.Peek(31) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s16, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x83d

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe4b;
      assert s11.Peek(16) == 0x83d;
      assert s11.Peek(25) == 0x546;
      assert s11.Peek(28) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe4b;
      assert s21.Peek(14) == 0x83d;
      assert s21.Peek(23) == 0x546;
      assert s21.Peek(26) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s27, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 180
    * Starting at 0xe4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[10] == 0x83d

    requires s0.stack[19] == 0x546

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup9(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x80);
      assert s11.Peek(13) == 0x83d;
      assert s11.Peek(22) == 0x546;
      assert s11.Peek(25) == 0x137;
      var s12 := Dup11(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(13) == 0x83d;
      assert s21.Peek(22) == 0x546;
      assert s21.Peek(25) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Push0(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s94(s31, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 181
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x546

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e9d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s7, gas - 1)
      else
        ExecuteFromCFGNode_s95(s7, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 182
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x546

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(14) == 0x83d;
      assert s11.Peek(23) == 0x546;
      assert s11.Peek(26) == 0x137;
      var s12 := MStore(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Dup7(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x546;
      assert s21.Peek(24) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap4(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap4(s24);
      var s26 := Swap1(s25);
      var s27 := Swap4(s26);
      var s28 := Add(s27);
      var s29 := Swap3(s28);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(12) == 0x83d;
      assert s31.Peek(21) == 0x546;
      assert s31.Peek(24) == 0x137;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0e6b);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s35, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 183
    * Starting at 0xe9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x546

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup10(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(12) == 0x83d;
      assert s11.Peek(21) == 0x546;
      assert s11.Peek(24) == 0x137;
      var s12 := And(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x80);
      var s18 := Dup10(s17);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup9(s20);
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x546;
      assert s21.Peek(24) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Sub(s22);
      var s24 := Dup4(s23);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup11(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Swap6(s29);
      var s31 := Pop(s30);
      assert s31.Peek(10) == 0x83d;
      assert s31.Peek(19) == 0x546;
      assert s31.Peek(22) == 0x137;
      var s32 := Push2(s31, 0x0ecc);
      var s33 := Dup2(s32);
      var s34 := Dup8(s33);
      var s35 := Push2(s34, 0x0dc0);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s36, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0xecc

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s98(s8, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x83d

    requires s0.stack[25] == 0x546

    requires s0.stack[28] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s7, gas - 1)
      else
        ExecuteFromCFGNode_s99(s7, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x83d

    requires s0.stack[25] == 0x546

    requires s0.stack[28] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xecc;
      assert s11.Peek(20) == 0x83d;
      assert s11.Peek(29) == 0x546;
      assert s11.Peek(32) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s16, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x83d

    requires s0.stack[25] == 0x546

    requires s0.stack[28] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xecc;
      assert s11.Peek(17) == 0x83d;
      assert s11.Peek(26) == 0x546;
      assert s11.Peek(29) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xecc;
      assert s21.Peek(15) == 0x83d;
      assert s21.Peek(24) == 0x546;
      assert s21.Peek(27) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s27, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 184
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x546

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x83d;
      assert s11.Peek(12) == 0x546;
      assert s11.Peek(15) == 0x137;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s14, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 109
    * Starting at 0x83d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x546

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(10) == 0x546;
      assert s11.Peek(13) == 0x137;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0858);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s16, gas - 1)
      else
        ExecuteFromCFGNode_s103(s16, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 110
    * Starting at 0x851
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x851 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 104
    * Segment Id for this node is: 111
    * Starting at 0x858
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x858 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(10) == 0x546;
      assert s11.Peek(13) == 0x137;
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
      assert s21.Peek(9) == 0x546;
      assert s21.Peek(12) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x087c);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0eda);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s28, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 185
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x87c

    requires s0.stack[9] == 0x546

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0eea);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s10, gas - 1)
      else
        ExecuteFromCFGNode_s106(s10, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 186
    * Starting at 0xee7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x87c

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

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

  /** Node 107
    * Segment Id for this node is: 187
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x87c

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s7, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 112
    * Starting at 0x87c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Dup4(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x091f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s8, gas - 1)
      else
        ExecuteFromCFGNode_s109(s8, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 113
    * Starting at 0x886
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x886 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x23b872dd);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(10) == 0x546;
      assert s11.Peek(13) == 0x137;
      var s12 := MStore(s11);
      var s13 := Address(s12);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup2(s18);
      var s20 := Add(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x546;
      assert s21.Peek(13) == 0x137;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Push32(s23, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(9) == 0x546;
      assert s31.Peek(12) == 0x137;
      var s32 := Push4(s31, 0x23b872dd);
      var s33 := Swap1(s32);
      var s34 := Push1(s33, 0x64);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x20);
      var s37 := Push1(s36, 0x40);
      var s38 := MLoad(s37);
      var s39 := Dup1(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      assert s41.Peek(13) == 0x546;
      assert s41.Peek(16) == 0x137;
      var s42 := Dup2(s41);
      var s43 := Push0(s42);
      var s44 := Dup8(s43);
      var s45 := Gas(s44);
      var s46 := Call(s45);
      var s47 := IsZero(s46);
      var s48 := Dup1(s47);
      var s49 := IsZero(s48);
      var s50 := Push2(s49, 0x08f5);
      var s51 := JumpI(s50);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s50.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s51, gas - 1)
      else
        ExecuteFromCFGNode_s110(s51, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 114
    * Starting at 0x8ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 111
    * Segment Id for this node is: 115
    * Starting at 0x8f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(11) == 0x546;
      assert s11.Peek(14) == 0x137;
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
      assert s21.Peek(10) == 0x546;
      assert s21.Peek(13) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0919);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1125);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s28, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 233
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x919

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1135);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s10, gas - 1)
      else
        ExecuteFromCFGNode_s113(s10, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 234
    * Starting at 0x1132
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x919

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

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

  /** Node 114
    * Segment Id for this node is: 235
    * Starting at 0x1135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x919

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0cbd);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0cdf);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s7, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 151
    * Starting at 0xcdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x919

    requires s0.stack[14] == 0x546

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x048c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s8, gas - 1)
      else
        ExecuteFromCFGNode_s116(s8, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 152
    * Starting at 0xce9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x919

    requires s0.stack[14] == 0x546

    requires s0.stack[17] == 0x137

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

  /** Node 117
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x919

    requires s0.stack[14] == 0x546

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s3, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x919

    requires s0.stack[12] == 0x546

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s7, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 116
    * Starting at 0x919
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x919 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x09a2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s4, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 124
    * Starting at 0x9a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x96f4e9f9);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(11) == 0x546;
      assert s11.Peek(14) == 0x137;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := Push32(s13, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Push4(s16, 0x96f4e9f9);
      var s18 := Swap1(s17);
      var s19 := Dup4(s18);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x09f2);
      assert s21.Peek(0) == 0x9f2;
      assert s21.Peek(12) == 0x546;
      assert s21.Peek(15) == 0x137;
      var s22 := Swap1(s21);
      var s23 := Dup12(s22);
      var s24 := Swap1(s23);
      var s25 := Dup9(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0e03);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s30, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 178
    * Starting at 0xe03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x9f2

    requires s0.stack[14] == 0x546

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x9f2;
      assert s11.Peek(18) == 0x546;
      assert s11.Peek(21) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup5(s18);
      var s20 := MLoad(s19);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(8) == 0x9f2;
      assert s21.Peek(19) == 0x546;
      assert s21.Peek(22) == 0x137;
      var s22 := Dup4(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0e2e);
      var s27 := Push1(s26, 0xe0);
      var s28 := Dup7(s27);
      var s29 := Add(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0dc0);
      assert s31.Peek(0) == 0xdc0;
      assert s31.Peek(3) == 0xe2e;
      assert s31.Peek(11) == 0x9f2;
      assert s31.Peek(22) == 0x546;
      assert s31.Peek(25) == 0x137;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s32, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xe2e

    requires s0.stack[10] == 0x9f2

    requires s0.stack[21] == 0x546

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s123(s8, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s7, gas - 1)
      else
        ExecuteFromCFGNode_s124(s7, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe2e;
      assert s11.Peek(17) == 0x9f2;
      assert s11.Peek(28) == 0x546;
      assert s11.Peek(31) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s16, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe2e;
      assert s11.Peek(14) == 0x9f2;
      assert s11.Peek(25) == 0x546;
      assert s11.Peek(28) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe2e;
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x546;
      assert s21.Peek(26) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s27, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 179
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[8] == 0x9f2

    requires s0.stack[19] == 0x546

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x3f);
      var s9 := Not(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(11) == 0x9f2;
      assert s11.Peek(22) == 0x546;
      assert s11.Peek(25) == 0x137;
      var s12 := Dup5(s11);
      var s13 := Sub(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push2(s18, 0x0e4b);
      var s20 := Dup4(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(2) == 0xe4b;
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x546;
      assert s21.Peek(26) == 0x137;
      var s22 := Push2(s21, 0x0dc0);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s23, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0xe4b

    requires s0.stack[12] == 0x9f2

    requires s0.stack[23] == 0x546

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s128(s8, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x9f2

    requires s0.stack[26] == 0x546

    requires s0.stack[29] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s7, gas - 1)
      else
        ExecuteFromCFGNode_s129(s7, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x9f2

    requires s0.stack[26] == 0x546

    requires s0.stack[29] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe4b;
      assert s11.Peek(19) == 0x9f2;
      assert s11.Peek(30) == 0x546;
      assert s11.Peek(33) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s16, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x9f2

    requires s0.stack[26] == 0x546

    requires s0.stack[29] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe4b;
      assert s11.Peek(16) == 0x9f2;
      assert s11.Peek(27) == 0x546;
      assert s11.Peek(30) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe4b;
      assert s21.Peek(14) == 0x9f2;
      assert s21.Peek(25) == 0x546;
      assert s21.Peek(28) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s27, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 180
    * Starting at 0xe4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[10] == 0x9f2

    requires s0.stack[21] == 0x546

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup9(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x80);
      assert s11.Peek(13) == 0x9f2;
      assert s11.Peek(24) == 0x546;
      assert s11.Peek(27) == 0x137;
      var s12 := Dup11(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(13) == 0x9f2;
      assert s21.Peek(24) == 0x546;
      assert s21.Peek(27) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Push0(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s132(s31, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 181
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e9d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s7, gas - 1)
      else
        ExecuteFromCFGNode_s133(s7, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 182
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(14) == 0x9f2;
      assert s11.Peek(25) == 0x546;
      assert s11.Peek(28) == 0x137;
      var s12 := MStore(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Dup7(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x546;
      assert s21.Peek(26) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap4(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap4(s24);
      var s26 := Swap1(s25);
      var s27 := Swap4(s26);
      var s28 := Add(s27);
      var s29 := Swap3(s28);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(12) == 0x9f2;
      assert s31.Peek(23) == 0x546;
      assert s31.Peek(26) == 0x137;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0e6b);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s35, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 183
    * Starting at 0xe9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup10(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(12) == 0x9f2;
      assert s11.Peek(23) == 0x546;
      assert s11.Peek(26) == 0x137;
      var s12 := And(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x80);
      var s18 := Dup10(s17);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup9(s20);
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x546;
      assert s21.Peek(26) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Sub(s22);
      var s24 := Dup4(s23);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup11(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Swap6(s29);
      var s31 := Pop(s30);
      assert s31.Peek(10) == 0x9f2;
      assert s31.Peek(21) == 0x546;
      assert s31.Peek(24) == 0x137;
      var s32 := Push2(s31, 0x0ecc);
      var s33 := Dup2(s32);
      var s34 := Dup8(s33);
      var s35 := Push2(s34, 0x0dc0);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s36, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0xecc

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x546

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s136(s8, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x9f2

    requires s0.stack[27] == 0x546

    requires s0.stack[30] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s7, gas - 1)
      else
        ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x9f2

    requires s0.stack[27] == 0x546

    requires s0.stack[30] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xecc;
      assert s11.Peek(20) == 0x9f2;
      assert s11.Peek(31) == 0x546;
      assert s11.Peek(34) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s16, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x9f2

    requires s0.stack[27] == 0x546

    requires s0.stack[30] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xecc;
      assert s11.Peek(17) == 0x9f2;
      assert s11.Peek(28) == 0x546;
      assert s11.Peek(31) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xecc;
      assert s21.Peek(15) == 0x9f2;
      assert s21.Peek(26) == 0x546;
      assert s21.Peek(29) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s27, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 184
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x546

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x9f2;
      assert s11.Peek(14) == 0x546;
      assert s11.Peek(17) == 0x137;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s14, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 125
    * Starting at 0x9f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Dup9(s9);
      var s11 := Gas(s10);
      assert s11.Peek(18) == 0x546;
      assert s11.Peek(21) == 0x137;
      var s12 := Call(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0a0e);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s142(s17, gas - 1)
      else
        ExecuteFromCFGNode_s141(s17, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 126
    * Starting at 0xa07
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x546

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 142
    * Segment Id for this node is: 127
    * Starting at 0xa0e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x546

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := ReturnDataSize(s8);
      var s10 := Push1(s9, 0x1f);
      var s11 := Not(s10);
      assert s11.Peek(10) == 0x546;
      assert s11.Peek(13) == 0x137;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(9) == 0x546;
      assert s21.Peek(12) == 0x137;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x0a33);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0eda);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s29, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 185
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0xa33

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0eea);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s10, gas - 1)
      else
        ExecuteFromCFGNode_s144(s10, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 186
    * Starting at 0xee7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa33

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

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

  /** Node 145
    * Segment Id for this node is: 187
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0xa33

    requires s0.stack[11] == 0x546

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s7, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 128
    * Starting at 0xa33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xf105803bee01dee7039d5715e807acca02889381ddf6041ddc55af0c68b4fc86);
      var s5 := Swap1(s4);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := Log2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(4) == 0x546;
      assert s11.Peek(7) == 0x137;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s16, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 87
    * Starting at 0x546
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x546 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s4, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 32
    * Starting at 0x137
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137 as nat
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

  /** Node 149
    * Segment Id for this node is: 117
    * Starting at 0x91f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Dup1(s4);
      var s6 := CallValue(s5);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0965);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s10, gas - 1)
      else
        ExecuteFromCFGNode_s150(s10, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 118
    * Starting at 0x92b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(10) == 0x546;
      assert s11.Peek(13) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x10);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 16, 0x696e73756666696369656e7420666565);
      var s19 := Push1(s18, 0x80);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(10) == 0x546;
      assert s21.Peek(13) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0501);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s28, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 83
    * Starting at 0x501
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

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
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 152
    * Segment Id for this node is: 119
    * Starting at 0x965
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x965 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallValue(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x09a2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s120(s7, gas - 1)
      else
        ExecuteFromCFGNode_s153(s7, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 120
    * Starting at 0x96e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := Push2(s1, 0x08fc);
      var s3 := Push2(s2, 0x097b);
      var s4 := Dup4(s3);
      var s5 := CallValue(s4);
      var s6 := Push2(s5, 0x1140);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s7, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 236
    * Starting at 0x1140
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x97b

    requires s0.stack[12] == 0x546

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02cc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s156(s10, gas - 1)
      else
        ExecuteFromCFGNode_s155(s10, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 237
    * Starting at 0x114c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x97b

    requires s0.stack[13] == 0x546

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 156
    * Segment Id for this node is: 64
    * Starting at 0x2cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x97b

    requires s0.stack[13] == 0x546

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s6, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 121
    * Starting at 0x97b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x546

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Mul(s7);
      var s9 := Swap2(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(13) == 0x546;
      assert s11.Peek(16) == 0x137;
      var s12 := Dup2(s11);
      var s13 := Dup2(s12);
      var s14 := Dup6(s13);
      var s15 := Dup9(s14);
      var s16 := Dup9(s15);
      var s17 := Call(s16);
      var s18 := Swap4(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(9) == 0x546;
      assert s21.Peek(12) == 0x137;
      var s22 := Pop(s21);
      var s23 := IsZero(s22);
      var s24 := Dup1(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x09a0);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s27, gas - 1)
      else
        ExecuteFromCFGNode_s158(s27, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 122
    * Starting at 0x999
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x999 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 159
    * Segment Id for this node is: 123
    * Starting at 0x9a0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x546

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s2, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 106
    * Starting at 0x79e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[7] == 0x546

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push32(s1, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s2, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 54
    * Starting at 0x261
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x261 as nat
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
      var s5 := Push2(s4, 0x026c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s6, gas - 1)
      else
        ExecuteFromCFGNode_s162(s6, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 55
    * Starting at 0x269
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
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

  /** Node 163
    * Segment Id for this node is: 56
    * Starting at 0x26c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0116);
      var s4 := Push2(s3, 0x054a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s5, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 88
    * Starting at 0x54a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0575);
      var s4 := Push32(s3, 0x000000000000000000000000000000000000000000000000383a1891ae1915b1);
      var s5 := Push0(s4);
      var s6 := Push2(s5, 0x02d2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s7, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 51
    * Starting at 0x22e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22e as nat
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
      var s5 := Push2(s4, 0x0239);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s6, gas - 1)
      else
        ExecuteFromCFGNode_s166(s6, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 52
    * Starting at 0x236
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
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

  /** Node 167
    * Segment Id for this node is: 53
    * Starting at 0x239
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x239 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x01b1);
      var s4 := Push32(s3, 0x000000000000000000000000ab534a239459ef03c9a389039463c7631075ecaa);
      var s5 := Dup2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 44
    * Starting at 0x1b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b1

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
      assert s11.Peek(2) == 0x1b1;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x00ee);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s17, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 24
    * Starting at 0xee
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b1

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

  /** Node 170
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0xa515ac67);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x017e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s181(s6, gas - 1)
      else
        ExecuteFromCFGNode_s171(s6, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 9
    * Starting at 0x63
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa66bf0d6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01c9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s178(s5, gas - 1)
      else
        ExecuteFromCFGNode_s172(s5, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 10
    * Starting at 0x6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xb0f479a1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01fc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s5, gas - 1)
      else
        ExecuteFromCFGNode_s173(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 11
    * Starting at 0x79
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
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

  /** Node 174
    * Segment Id for this node is: 48
    * Starting at 0x1fc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fc as nat
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
      var s5 := Push2(s4, 0x0207);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s6, gas - 1)
      else
        ExecuteFromCFGNode_s175(s6, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 49
    * Starting at 0x204
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x204 as nat
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

  /** Node 176
    * Segment Id for this node is: 50
    * Starting at 0x207
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push32(s2, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s4 := Push2(s3, 0x01b1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s5, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 44
    * Starting at 0x1b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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
      var s16 := Push2(s15, 0x00ee);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s17, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 45
    * Starting at 0x1c9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c9 as nat
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
      var s5 := Push2(s4, 0x01d4);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s180(s6, gas - 1)
      else
        ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 46
    * Starting at 0x1d1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d1 as nat
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

  /** Node 180
    * Segment Id for this node is: 47
    * Starting at 0x1d4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x01b1);
      var s4 := Push32(s3, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      var s5 := Dup2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 41
    * Starting at 0x17e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17e as nat
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
      var s5 := Push2(s4, 0x0189);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s6, gas - 1)
      else
        ExecuteFromCFGNode_s182(s6, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 42
    * Starting at 0x186
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x186 as nat
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

  /** Node 183
    * Segment Id for this node is: 43
    * Starting at 0x189
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x189 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x01b1);
      var s4 := Push32(s3, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s5 := Dup2(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 12
    * Starting at 0x7c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x01ffc9a7);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00c3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s489(s6, gas - 1)
      else
        ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1b67b1b8);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00f7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s440(s5, gas - 1)
      else
        ExecuteFromCFGNode_s186(s5, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x2be94d6d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0124);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s434(s5, gas - 1)
      else
        ExecuteFromCFGNode_s187(s5, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 15
    * Starting at 0x9e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x5264cb9e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0139);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s5, gas - 1)
      else
        ExecuteFromCFGNode_s188(s5, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 16
    * Starting at 0xa9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x85572ffb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x014c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s201(s5, gas - 1)
      else
        ExecuteFromCFGNode_s189(s5, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 17
    * Starting at 0xb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x9a9cecc9);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x016b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s5, gas - 1)
      else
        ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 18
    * Starting at 0xbf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf as nat
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

  /** Node 191
    * Segment Id for this node is: 39
    * Starting at 0x16b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0137);
      var s3 := Push2(s2, 0x0179);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d82);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 169
    * Starting at 0xd82
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x179

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0d93);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s11, gas - 1)
      else
        ExecuteFromCFGNode_s193(s11, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 170
    * Starting at 0xd90
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x179

    requires s0.stack[5] == 0x137

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

  /** Node 194
    * Segment Id for this node is: 171
    * Starting at 0xd93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x179

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0d9e);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0d6e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s7, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 167
    * Starting at 0xd6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd9e

    requires s0.stack[7] == 0x179

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x048c);
      assert s11.Peek(0) == 0x48c;
      assert s11.Peek(3) == 0xd9e;
      assert s11.Peek(9) == 0x179;
      assert s11.Peek(10) == 0x137;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s12, gas - 1)
      else
        ExecuteFromCFGNode_s196(s12, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 168
    * Starting at 0xd7f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd9e

    requires s0.stack[7] == 0x179

    requires s0.stack[8] == 0x137

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

  /** Node 197
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd9e

    requires s0.stack[7] == 0x179

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s3, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 172
    * Starting at 0xd9e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x179

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(1) == 0x179;
      assert s11.Peek(4) == 0x137;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s13, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 40
    * Starting at 0x179
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x051b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s3, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 86
    * Starting at 0x51b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0546);
      var s3 := Push32(s2, 0x0000000000000000000000000000000000000000000000009d70576d8e253bcf);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x060d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s7, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 35
    * Starting at 0x14c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c as nat
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
      var s5 := Push2(s4, 0x0157);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s203(s6, gas - 1)
      else
        ExecuteFromCFGNode_s202(s6, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 36
    * Starting at 0x154
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154 as nat
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

  /** Node 203
    * Segment Id for this node is: 37
    * Starting at 0x157
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0137);
      var s4 := Push2(s3, 0x0166);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0d38);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s8, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 161
    * Starting at 0xd38
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd38 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x166

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d48);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s10, gas - 1)
      else
        ExecuteFromCFGNode_s205(s10, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 162
    * Starting at 0xd45
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x166

    requires s0.stack[4] == 0x137

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

  /** Node 206
    * Segment Id for this node is: 163
    * Starting at 0xd48
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x166

    requires s0.stack[4] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(5) == 0x166;
      assert s11.Peek(6) == 0x137;
      var s12 := Push2(s11, 0x0d5d);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s13, gas - 1)
      else
        ExecuteFromCFGNode_s207(s13, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 164
    * Starting at 0xd5a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x166

    requires s0.stack[5] == 0x137

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

  /** Node 208
    * Segment Id for this node is: 165
    * Starting at 0xd5d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x166

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cbd);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s210(s11, gas - 1)
      else
        ExecuteFromCFGNode_s209(s11, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 166
    * Starting at 0xd6b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x166

    requires s0.stack[5] == 0x137

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

  /** Node 210
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x166

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
    * Segment Id for this node is: 38
    * Starting at 0x166
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x166 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x04ba);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s3, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 81
    * Starting at 0x4ba
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Caller(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Push32(s7, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s9 := And(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x050a);
      assert s11.Peek(0) == 0x50a;
      assert s11.Peek(3) == 0x137;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s12, gas - 1)
      else
        ExecuteFromCFGNode_s213(s12, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 82
    * Starting at 0x4eb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x35fdcccd);
      var s4 := Push1(s3, 0xe2);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x24);
      var s14 := Add(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s214(s14, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 83
    * Starting at 0x501
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

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
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 215
    * Segment Id for this node is: 84
    * Starting at 0x50a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x048c);
      var s3 := Push2(s2, 0x0516);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x107e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s6, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 219
    * Starting at 0x107e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x516

    requires s0.stack[2] == 0x48c

    requires s0.stack[4] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0xa0);
      var s4 := Dup3(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x108e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s10, gas - 1)
      else
        ExecuteFromCFGNode_s217(s10, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 220
    * Starting at 0x108b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x516

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

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

  /** Node 218
    * Segment Id for this node is: 221
    * Starting at 0x108e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x516

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x1096);
      var s3 := Push2(s2, 0x0f19);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s4, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 191
    * Starting at 0xf19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x1096

    requires s0.stack[3] == 0x516

    requires s0.stack[4] == 0x48c

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x40);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(3) == 0x1096;
      assert s11.Peek(6) == 0x516;
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
      var s12 := Dup2(s11);
      var s13 := Gt(s12);
      var s14 := Dup3(s13);
      var s15 := Dup3(s14);
      var s16 := Lt(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x0f13);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s222(s20, gas - 1)
      else
        ExecuteFromCFGNode_s220(s20, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 192
    * Starting at 0xf34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1096

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f13);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s3, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0xf13

    requires s0.stack[3] == 0x1096

    requires s0.stack[6] == 0x516

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf13;
      assert s11.Peek(5) == 0x1096;
      assert s11.Peek(8) == 0x516;
      assert s11.Peek(9) == 0x48c;
      assert s11.Peek(11) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 222
    * Segment Id for this node is: 190
    * Starting at 0xf13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1096

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s5, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 222
    * Starting at 0x1096
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1096 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x516

    requires s0.stack[4] == 0x48c

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x10a6);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0cc4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s11, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 148
    * Starting at 0xcc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x10a6

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x10a6;
      assert s11.Peek(8) == 0x516;
      assert s11.Peek(9) == 0x48c;
      assert s11.Peek(11) == 0x137;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0cda);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s14, gas - 1)
      else
        ExecuteFromCFGNode_s225(s14, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 149
    * Starting at 0xcd7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x10a6

    requires s0.stack[6] == 0x516

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

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

  /** Node 226
    * Segment Id for this node is: 150
    * Starting at 0xcda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x10a6

    requires s0.stack[6] == 0x516

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s5, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 223
    * Starting at 0x10a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x516

    requires s0.stack[5] == 0x48c

    requires s0.stack[7] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(6) == 0x516;
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
      var s12 := Push1(s11, 0x40);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Gt(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x10c4);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s20, gas - 1)
      else
        ExecuteFromCFGNode_s228(s20, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 224
    * Starting at 0x10c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

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

  /** Node 229
    * Segment Id for this node is: 225
    * Starting at 0x10c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x10d0);
      var s3 := CallDataSize(s2);
      var s4 := Dup4(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0f6b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s8, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 196
    * Starting at 0xf6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x10d0

    requires s0.stack[8] == 0x516

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0f7a);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s232(s9, gas - 1)
      else
        ExecuteFromCFGNode_s231(s9, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 197
    * Starting at 0xf77
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x10d0

    requires s0.stack[9] == 0x516

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

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

  /** Node 232
    * Segment Id for this node is: 198
    * Starting at 0xf7a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x10d0

    requires s0.stack[9] == 0x516

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(5) == 0x10d0;
      assert s11.Peek(11) == 0x516;
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := Push2(s11, 0x0f93);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s13, gas - 1)
      else
        ExecuteFromCFGNode_s233(s13, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 199
    * Starting at 0xf8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x10d0

    requires s0.stack[10] == 0x516

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f93);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s3, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xf93

    requires s0.stack[5] == 0x10d0

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf93;
      assert s11.Peek(7) == 0x10d0;
      assert s11.Peek(13) == 0x516;
      assert s11.Peek(14) == 0x48c;
      assert s11.Peek(16) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 235
    * Segment Id for this node is: 200
    * Starting at 0xf93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x10d0

    requires s0.stack[10] == 0x516

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0fa6);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Not(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0f3b);
      assert s11.Peek(0) == 0xf3b;
      assert s11.Peek(2) == 0xfa6;
      assert s11.Peek(7) == 0x10d0;
      assert s11.Peek(13) == 0x516;
      assert s11.Peek(14) == 0x48c;
      assert s11.Peek(16) == 0x137;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s12, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 193
    * Starting at 0xf3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xfa6

    requires s0.stack[6] == 0x10d0

    requires s0.stack[12] == 0x516

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0xfa6;
      assert s11.Peek(8) == 0x10d0;
      assert s11.Peek(14) == 0x516;
      assert s11.Peek(15) == 0x48c;
      assert s11.Peek(17) == 0x137;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0xfa6;
      assert s21.Peek(10) == 0x10d0;
      assert s21.Peek(16) == 0x516;
      assert s21.Peek(17) == 0x48c;
      assert s21.Peek(19) == 0x137;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0f63);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s25, gas - 1)
      else
        ExecuteFromCFGNode_s237(s25, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 194
    * Starting at 0xf5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xfa6

    requires s0.stack[8] == 0x10d0

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f63);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s3, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xf63

    requires s0.stack[4] == 0xfa6

    requires s0.stack[9] == 0x10d0

    requires s0.stack[15] == 0x516

    requires s0.stack[16] == 0x48c

    requires s0.stack[18] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf63;
      assert s11.Peek(6) == 0xfa6;
      assert s11.Peek(11) == 0x10d0;
      assert s11.Peek(17) == 0x516;
      assert s11.Peek(18) == 0x48c;
      assert s11.Peek(20) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 239
    * Segment Id for this node is: 195
    * Starting at 0xf63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xfa6

    requires s0.stack[8] == 0x10d0

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s7, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 201
    * Starting at 0xfa6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x10d0

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0x10d0;
      assert s11.Peek(12) == 0x516;
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0fba);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s14, gas - 1)
      else
        ExecuteFromCFGNode_s241(s14, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 202
    * Starting at 0xfb7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x10d0

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

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

  /** Node 242
    * Segment Id for this node is: 203
    * Starting at 0xfba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x10d0

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push0(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x10d0;
      assert s11.Peek(12) == 0x516;
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(3) == 0x10d0;
      assert s21.Peek(10) == 0x516;
      assert s21.Peek(11) == 0x48c;
      assert s21.Peek(13) == 0x137;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s25, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 226
    * Starting at 0x10d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x516

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup6(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x516;
      assert s11.Peek(6) == 0x48c;
      assert s11.Peek(8) == 0x137;
      var s12 := Dup1(s11);
      var s13 := Dup3(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x10e8);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s245(s17, gas - 1)
      else
        ExecuteFromCFGNode_s244(s17, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 227
    * Starting at 0x10e5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

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

  /** Node 245
    * Segment Id for this node is: 228
    * Starting at 0x10e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x10f4);
      var s3 := CallDataSize(s2);
      var s4 := Dup4(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0f6b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s8, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 196
    * Starting at 0xf6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x10f4

    requires s0.stack[8] == 0x516

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0f7a);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s9, gas - 1)
      else
        ExecuteFromCFGNode_s247(s9, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 197
    * Starting at 0xf77
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf77 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x10f4

    requires s0.stack[9] == 0x516

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

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

  /** Node 248
    * Segment Id for this node is: 198
    * Starting at 0xf7a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x10f4

    requires s0.stack[9] == 0x516

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(5) == 0x10f4;
      assert s11.Peek(11) == 0x516;
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := Push2(s11, 0x0f93);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s13, gas - 1)
      else
        ExecuteFromCFGNode_s249(s13, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 199
    * Starting at 0xf8c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x10f4

    requires s0.stack[10] == 0x516

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f93);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s3, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0xf93

    requires s0.stack[5] == 0x10f4

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf93;
      assert s11.Peek(7) == 0x10f4;
      assert s11.Peek(13) == 0x516;
      assert s11.Peek(14) == 0x48c;
      assert s11.Peek(16) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 251
    * Segment Id for this node is: 200
    * Starting at 0xf93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x10f4

    requires s0.stack[10] == 0x516

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0fa6);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Not(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0f3b);
      assert s11.Peek(0) == 0xf3b;
      assert s11.Peek(2) == 0xfa6;
      assert s11.Peek(7) == 0x10f4;
      assert s11.Peek(13) == 0x516;
      assert s11.Peek(14) == 0x48c;
      assert s11.Peek(16) == 0x137;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s12, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 193
    * Starting at 0xf3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0xfa6

    requires s0.stack[6] == 0x10f4

    requires s0.stack[12] == 0x516

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0xfa6;
      assert s11.Peek(8) == 0x10f4;
      assert s11.Peek(14) == 0x516;
      assert s11.Peek(15) == 0x48c;
      assert s11.Peek(17) == 0x137;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0xfa6;
      assert s21.Peek(10) == 0x10f4;
      assert s21.Peek(16) == 0x516;
      assert s21.Peek(17) == 0x48c;
      assert s21.Peek(19) == 0x137;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0f63);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s25, gas - 1)
      else
        ExecuteFromCFGNode_s253(s25, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 194
    * Starting at 0xf5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xfa6

    requires s0.stack[8] == 0x10f4

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f63);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s3, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xf63

    requires s0.stack[4] == 0xfa6

    requires s0.stack[9] == 0x10f4

    requires s0.stack[15] == 0x516

    requires s0.stack[16] == 0x48c

    requires s0.stack[18] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf63;
      assert s11.Peek(6) == 0xfa6;
      assert s11.Peek(11) == 0x10f4;
      assert s11.Peek(17) == 0x516;
      assert s11.Peek(18) == 0x48c;
      assert s11.Peek(20) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 255
    * Segment Id for this node is: 195
    * Starting at 0xf63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xfa6

    requires s0.stack[8] == 0x10f4

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s7, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 201
    * Starting at 0xfa6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x10f4

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0x10f4;
      assert s11.Peek(12) == 0x516;
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0fba);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s14, gas - 1)
      else
        ExecuteFromCFGNode_s257(s14, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 202
    * Starting at 0xfb7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x10f4

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

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

  /** Node 258
    * Segment Id for this node is: 203
    * Starting at 0xfba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x10f4

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push0(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(6) == 0x10f4;
      assert s11.Peek(12) == 0x516;
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(3) == 0x10f4;
      assert s21.Peek(10) == 0x516;
      assert s21.Peek(11) == 0x48c;
      assert s21.Peek(13) == 0x137;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s25, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 229
    * Starting at 0x10f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x516

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x60);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup6(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x516;
      assert s11.Peek(6) == 0x48c;
      assert s11.Peek(8) == 0x137;
      var s12 := Dup1(s11);
      var s13 := Dup3(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x110c);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s17, gas - 1)
      else
        ExecuteFromCFGNode_s260(s17, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 230
    * Starting at 0x1109
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

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

  /** Node 261
    * Segment Id for this node is: 231
    * Starting at 0x110c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x1119);
      var s4 := CallDataSize(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0fd6);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s9, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 204
    * Starting at 0xfd6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1119

    requires s0.stack[7] == 0x516

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0fe5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s264(s9, gas - 1)
      else
        ExecuteFromCFGNode_s263(s9, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 205
    * Starting at 0xfe2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1119

    requires s0.stack[8] == 0x516

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

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

  /** Node 264
    * Segment Id for this node is: 206
    * Starting at 0xfe5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1119

    requires s0.stack[8] == 0x516

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x40);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0x1119;
      assert s11.Peek(11) == 0x516;
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1000);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s14, gas - 1)
      else
        ExecuteFromCFGNode_s265(s14, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 207
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x1119

    requires s0.stack[10] == 0x516

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1000);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s3, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x1000

    requires s0.stack[6] == 0x1119

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0x1000;
      assert s11.Peek(8) == 0x1119;
      assert s11.Peek(13) == 0x516;
      assert s11.Peek(14) == 0x48c;
      assert s11.Peek(16) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 267
    * Segment Id for this node is: 208
    * Starting at 0x1000
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1000 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x1119

    requires s0.stack[10] == 0x516

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x100e);
      var s3 := Dup2(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x05);
      var s6 := Shl(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0f3b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s9, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 193
    * Starting at 0xf3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x100e

    requires s0.stack[7] == 0x1119

    requires s0.stack[12] == 0x516

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x100e;
      assert s11.Peek(9) == 0x1119;
      assert s11.Peek(14) == 0x516;
      assert s11.Peek(15) == 0x48c;
      assert s11.Peek(17) == 0x137;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x40);
      var s15 := Shl(s14);
      var s16 := Sub(s15);
      var s17 := Dup2(s16);
      var s18 := Gt(s17);
      var s19 := Dup3(s18);
      var s20 := Dup3(s19);
      var s21 := Lt(s20);
      assert s21.Peek(5) == 0x100e;
      assert s21.Peek(11) == 0x1119;
      assert s21.Peek(16) == 0x516;
      assert s21.Peek(17) == 0x48c;
      assert s21.Peek(19) == 0x137;
      var s22 := Or(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x0f63);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s25, gas - 1)
      else
        ExecuteFromCFGNode_s269(s25, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 194
    * Starting at 0xf5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x100e

    requires s0.stack[9] == 0x1119

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f63);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s3, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xf63

    requires s0.stack[4] == 0x100e

    requires s0.stack[10] == 0x1119

    requires s0.stack[15] == 0x516

    requires s0.stack[16] == 0x48c

    requires s0.stack[18] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf63;
      assert s11.Peek(6) == 0x100e;
      assert s11.Peek(12) == 0x1119;
      assert s11.Peek(17) == 0x516;
      assert s11.Peek(18) == 0x48c;
      assert s11.Peek(20) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 271
    * Segment Id for this node is: 195
    * Starting at 0xf63
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x100e

    requires s0.stack[9] == 0x1119

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s7, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 209
    * Starting at 0x100e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1119

    requires s0.stack[11] == 0x516

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x06);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Shl(s8);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x1119;
      assert s11.Peek(11) == 0x516;
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Dup7(s18);
      var s20 := Dup5(s19);
      var s21 := Gt(s20);
      assert s21.Peek(8) == 0x1119;
      assert s21.Peek(13) == 0x516;
      assert s21.Peek(14) == 0x48c;
      assert s21.Peek(16) == 0x137;
      var s22 := IsZero(s21);
      var s23 := Push2(s22, 0x102c);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s24, gas - 1)
      else
        ExecuteFromCFGNode_s273(s24, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 210
    * Starting at 0x1029
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1029 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x1119

    requires s0.stack[12] == 0x516

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

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

  /** Node 274
    * Segment Id for this node is: 211
    * Starting at 0x102c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x1119

    requires s0.stack[12] == 0x516

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s275(s4, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 212
    * Starting at 0x1030
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1030 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1119

    requires s0.stack[13] == 0x516

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup5(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x1073);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s288(s7, gas - 1)
      else
        ExecuteFromCFGNode_s276(s7, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 213
    * Starting at 0x1039
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1039 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1119

    requires s0.stack[13] == 0x516

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := Dup2(s1);
      var s3 := Dup10(s2);
      var s4 := Sub(s3);
      var s5 := SLt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x1048);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s8, gas - 1)
      else
        ExecuteFromCFGNode_s277(s8, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 214
    * Starting at 0x1044
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1044 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1119

    requires s0.stack[13] == 0x516

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Dup1(s1);
      var s3 := Dup2(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 278
    * Segment Id for this node is: 215
    * Starting at 0x1048
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1048 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1119

    requires s0.stack[13] == 0x516

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x1050);
      var s3 := Push2(s2, 0x0ef1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s4, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 188
    * Starting at 0xef1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x1050

    requires s0.stack[9] == 0x1119

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x40);
      var s11 := Shl(s10);
      assert s11.Peek(4) == 0x1050;
      assert s11.Peek(13) == 0x1119;
      assert s11.Peek(18) == 0x516;
      assert s11.Peek(19) == 0x48c;
      assert s11.Peek(21) == 0x137;
      var s12 := Sub(s11);
      var s13 := Dup2(s12);
      var s14 := Gt(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Lt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0f13);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s282(s21, gas - 1)
      else
        ExecuteFromCFGNode_s280(s21, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 189
    * Starting at 0xf0c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1050

    requires s0.stack[11] == 0x1119

    requires s0.stack[16] == 0x516

    requires s0.stack[17] == 0x48c

    requires s0.stack[19] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0f13);
      var s2 := Push2(s1, 0x0dac);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s3, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 173
    * Starting at 0xdac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0xf13

    requires s0.stack[3] == 0x1050

    requires s0.stack[12] == 0x1119

    requires s0.stack[17] == 0x516

    requires s0.stack[18] == 0x48c

    requires s0.stack[20] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(2) == 0xf13;
      assert s11.Peek(5) == 0x1050;
      assert s11.Peek(14) == 0x1119;
      assert s11.Peek(19) == 0x516;
      assert s11.Peek(20) == 0x48c;
      assert s11.Peek(22) == 0x137;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 282
    * Segment Id for this node is: 190
    * Starting at 0xf13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x1050

    requires s0.stack[11] == 0x1119

    requires s0.stack[16] == 0x516

    requires s0.stack[17] == 0x48c

    requires s0.stack[19] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s5, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 216
    * Starting at 0x1050
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1050 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[9] == 0x1119

    requires s0.stack[14] == 0x516

    requires s0.stack[15] == 0x48c

    requires s0.stack[17] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x105b);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0d6e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s7, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 167
    * Starting at 0xd6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x105b

    requires s0.stack[12] == 0x1119

    requires s0.stack[17] == 0x516

    requires s0.stack[18] == 0x48c

    requires s0.stack[20] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x048c);
      assert s11.Peek(0) == 0x48c;
      assert s11.Peek(3) == 0x105b;
      assert s11.Peek(14) == 0x1119;
      assert s11.Peek(19) == 0x516;
      assert s11.Peek(20) == 0x48c;
      assert s11.Peek(22) == 0x137;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s286(s12, gas - 1)
      else
        ExecuteFromCFGNode_s285(s12, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 168
    * Starting at 0xd7f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x105b

    requires s0.stack[12] == 0x1119

    requires s0.stack[17] == 0x516

    requires s0.stack[18] == 0x48c

    requires s0.stack[20] == 0x137

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

  /** Node 286
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x105b

    requires s0.stack[12] == 0x1119

    requires s0.stack[17] == 0x516

    requires s0.stack[18] == 0x48c

    requires s0.stack[20] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 217
    * Starting at 0x105b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x1119

    requires s0.stack[15] == 0x516

    requires s0.stack[16] == 0x48c

    requires s0.stack[18] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Dup2(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Dup6(s7);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(9) == 0x1119;
      assert s11.Peek(14) == 0x516;
      assert s11.Peek(15) == 0x48c;
      assert s11.Peek(17) == 0x137;
      var s12 := Dup4(s11);
      var s13 := MStore(s12);
      var s14 := Swap2(s13);
      var s15 := Dup4(s14);
      var s16 := Add(s15);
      var s17 := Swap2(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x1030);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s21, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 218
    * Starting at 0x1073
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1073 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1119

    requires s0.stack[13] == 0x516

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Swap7(s2);
      var s4 := Swap6(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s11, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 232
    * Starting at 0x1119
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1119 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x516

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x80);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s290(s11, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 85
    * Starting at 0x516
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x516 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x48c

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0a64);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s291(s3, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 129
    * Starting at 0xa64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x48c

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push32(s1, 0x0000000000000000000000000000000000000000000000009d70576d8e253bcf);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x40);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x48c;
      assert s11.Peek(5) == 0x137;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x40);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := And(s17);
      var s19 := Eq(s18);
      var s20 := Dup1(s19);
      var s21 := Push2(s20, 0x0add);
      assert s21.Peek(0) == 0xadd;
      assert s21.Peek(4) == 0x48c;
      assert s21.Peek(6) == 0x137;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s293(s22, gas - 1)
      else
        ExecuteFromCFGNode_s292(s22, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 130
    * Starting at 0xaa3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x48c

    requires s0.stack[4] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Push32(s1, 0x000000000000000000000000000000000000000000000000383a1891ae1915b1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x40);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x48c;
      assert s11.Peek(5) == 0x137;
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x40);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := And(s17);
      var s19 := Eq(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s293(s19, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 131
    * Starting at 0xadd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xadd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x48c

    requires s0.stack[4] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0b29);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s296(s3, gas - 1)
      else
        ExecuteFromCFGNode_s294(s3, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 132
    * Starting at 0xae2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x48c

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(4) == 0x48c;
      assert s11.Peek(6) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x18);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5468697320436861696e206e6f7420537570706f727465640000000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x48c;
      assert s21.Peek(6) == 0x137;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0501);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s26, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 83
    * Starting at 0x501
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x48c

    requires s0.stack[4] == 0x137

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
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 296
    * Segment Id for this node is: 133
    * Starting at 0xb29
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb29 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x48c

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Address(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x48c;
      assert s11.Peek(5) == 0x137;
      var s12 := MLoad(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := MLoad(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x0b4b);
      assert s21.Peek(0) == 0xb4b;
      assert s21.Peek(5) == 0x48c;
      assert s21.Peek(7) == 0x137;
      var s22 := Swap2(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x115f);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s297(s25, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 238
    * Starting at 0x115f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xb4b

    requires s0.stack[5] == 0x48c

    requires s0.stack[7] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x116f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s299(s10, gas - 1)
      else
        ExecuteFromCFGNode_s298(s10, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 239
    * Starting at 0x116c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xb4b

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

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

  /** Node 299
    * Segment Id for this node is: 240
    * Starting at 0x116f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xb4b

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0cbd);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0d6e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s300(s7, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 167
    * Starting at 0xd6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0xb4b

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x048c);
      assert s11.Peek(0) == 0x48c;
      assert s11.Peek(3) == 0xcbd;
      assert s11.Peek(8) == 0xb4b;
      assert s11.Peek(11) == 0x48c;
      assert s11.Peek(13) == 0x137;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s302(s12, gas - 1)
      else
        ExecuteFromCFGNode_s301(s12, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 168
    * Starting at 0xd7f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0xb4b

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

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

  /** Node 302
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0xb4b

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s303(s3, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xb4b

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s7, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 134
    * Starting at 0xb4b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0ba1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s306(s10, gas - 1)
      else
        ExecuteFromCFGNode_s305(s10, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 135
    * Starting at 0xb5a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x48c

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(4) == 0x48c;
      assert s11.Peek(6) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x17);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x20696e76616c6964206d6573736167652073656e646572000000000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x48c;
      assert s21.Peek(6) == 0x137;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0501);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s26, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 136
    * Starting at 0xba1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x48c

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x48c;
      assert s11.Peek(7) == 0x137;
      var s12 := MLoad(s11);
      var s13 := Dup2(s12);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Push2(s15, 0x0bbb);
      var s17 := Swap2(s16);
      var s18 := Swap1(s17);
      var s19 := Push2(s18, 0x117a);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s20, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 241
    * Starting at 0x117a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xbbb

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x118b);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s309(s11, gas - 1)
      else
        ExecuteFromCFGNode_s308(s11, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 242
    * Starting at 0x1188
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xbbb

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

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

  /** Node 309
    * Segment Id for this node is: 243
    * Starting at 0x118b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xbbb

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MLoad(s8);
      var s10 := Push2(s9, 0x0d16);
      var s11 := Dup2(s10);
      assert s11.Peek(1) == 0xd16;
      assert s11.Peek(7) == 0xbbb;
      assert s11.Peek(11) == 0x48c;
      assert s11.Peek(13) == 0x137;
      var s12 := Push2(s11, 0x0d6e);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s13, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 167
    * Starting at 0xd6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd16

    requires s0.stack[7] == 0xbbb

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x048c);
      assert s11.Peek(0) == 0x48c;
      assert s11.Peek(3) == 0xd16;
      assert s11.Peek(9) == 0xbbb;
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s312(s12, gas - 1)
      else
        ExecuteFromCFGNode_s311(s12, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 168
    * Starting at 0xd7f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd16

    requires s0.stack[7] == 0xbbb

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

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

  /** Node 312
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0xd16

    requires s0.stack[7] == 0xbbb

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s313(s3, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 157
    * Starting at 0xd16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xbbb

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      ExecuteFromCFGNode_s314(s11, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 137
    * Starting at 0xbbb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x48c

    requires s0.stack[7] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0xa9059cbb);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(9) == 0x48c;
      assert s11.Peek(11) == 0x137;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := Dup1(s13);
      var s15 := Dup4(s14);
      var s16 := And(s15);
      var s17 := Push1(s16, 0x04);
      var s18 := Dup4(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x24);
      assert s21.Peek(8) == 0x48c;
      assert s21.Peek(10) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := Dup5(s23);
      var s25 := Swap1(s24);
      var s26 := MStore(s25);
      var s27 := Swap3(s26);
      var s28 := Swap5(s27);
      var s29 := Pop(s28);
      var s30 := Swap1(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(6) == 0x48c;
      assert s31.Peek(8) == 0x137;
      var s32 := Pop(s31);
      var s33 := Push32(s32, 0x000000000000000000000000ab534a239459ef03c9a389039463c7631075ecaa);
      var s34 := Swap1(s33);
      var s35 := Swap2(s34);
      var s36 := And(s35);
      var s37 := Swap1(s36);
      var s38 := Push4(s37, 0xa9059cbb);
      var s39 := Swap1(s38);
      var s40 := Push1(s39, 0x44);
      var s41 := Add(s40);
      assert s41.Peek(6) == 0x48c;
      assert s41.Peek(8) == 0x137;
      var s42 := Push1(s41, 0x20);
      var s43 := Push1(s42, 0x40);
      var s44 := MLoad(s43);
      var s45 := Dup1(s44);
      var s46 := Dup4(s45);
      var s47 := Sub(s46);
      var s48 := Dup2(s47);
      var s49 := Push0(s48);
      var s50 := Dup8(s49);
      var s51 := Gas(s50);
      assert s51.Peek(13) == 0x48c;
      assert s51.Peek(15) == 0x137;
      var s52 := Call(s51);
      var s53 := IsZero(s52);
      var s54 := Dup1(s53);
      var s55 := IsZero(s54);
      var s56 := Push2(s55, 0x0c2f);
      var s57 := JumpI(s56);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s56.stack[1] > 0 then
        ExecuteFromCFGNode_s316(s57, gas - 1)
      else
        ExecuteFromCFGNode_s315(s57, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 138
    * Starting at 0xc28
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 316
    * Segment Id for this node is: 139
    * Starting at 0xc2f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
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
      assert s21.Peek(6) == 0x48c;
      assert s21.Peek(8) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0c53);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1125);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s28, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 233
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xc53

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1135);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s319(s10, gas - 1)
      else
        ExecuteFromCFGNode_s318(s10, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 234
    * Starting at 0x1132
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xc53

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

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

  /** Node 319
    * Segment Id for this node is: 235
    * Starting at 0x1135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xc53

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0cbd);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0cdf);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s7, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 151
    * Starting at 0xcdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0xc53

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x048c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s322(s8, gas - 1)
      else
        ExecuteFromCFGNode_s321(s8, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 152
    * Starting at 0xce9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0xc53

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

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

  /** Node 322
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0xc53

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s3, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xc53

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s324(s7, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 140
    * Starting at 0xc53
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x48c

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0c91);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s327(s3, gas - 1)
      else
        ExecuteFromCFGNode_s325(s3, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 141
    * Starting at 0xc58
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc58 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(6) == 0x48c;
      assert s11.Peek(8) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151c985b9cd9995c8819985a5b1959);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x48c;
      assert s21.Peek(8) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0501);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s28, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 83
    * Starting at 0x501
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x48c

    requires s0.stack[6] == 0x137

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
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 327
    * Segment Id for this node is: 142
    * Starting at 0xc91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s5, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s3, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 33
    * Starting at 0x139
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0137);
      var s3 := Push2(s2, 0x0147);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d21);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s7, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 158
    * Starting at 0xd21
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x147

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d31);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s10, gas - 1)
      else
        ExecuteFromCFGNode_s331(s10, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 159
    * Starting at 0xd2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x147

    requires s0.stack[4] == 0x137

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

  /** Node 332
    * Segment Id for this node is: 160
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x147

    requires s0.stack[4] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s7, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 34
    * Starting at 0x147
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x048f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s3, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 80
    * Starting at 0x48f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x048c);
      var s3 := Push32(s2, 0x000000000000000000000000000000000000000000000000383a1891ae1915b1);
      var s4 := Caller(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x060d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s7, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 93
    * Starting at 0x60d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x23b872dd);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Caller(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Address(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup2(s19);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x48c;
      assert s21.Peek(7) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Push32(s24, 0x000000000000000000000000ab534a239459ef03c9a389039463c7631075ecaa);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0xa0);
      var s29 := Shl(s28);
      var s30 := Sub(s29);
      var s31 := And(s30);
      assert s31.Peek(5) == 0x48c;
      assert s31.Peek(7) == 0x137;
      var s32 := Swap1(s31);
      var s33 := Push4(s32, 0x23b872dd);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x64);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Dup1(s39);
      var s41 := Dup4(s40);
      assert s41.Peek(10) == 0x48c;
      assert s41.Peek(12) == 0x137;
      var s42 := Sub(s41);
      var s43 := Dup2(s42);
      var s44 := Push0(s43);
      var s45 := Dup8(s44);
      var s46 := Gas(s45);
      var s47 := Call(s46);
      var s48 := IsZero(s47);
      var s49 := Dup1(s48);
      var s50 := IsZero(s49);
      var s51 := Push2(s50, 0x067d);
      assert s51.Peek(0) == 0x67d;
      assert s51.Peek(9) == 0x48c;
      assert s51.Peek(11) == 0x137;
      var s52 := JumpI(s51);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s51.stack[1] > 0 then
        ExecuteFromCFGNode_s337(s52, gas - 1)
      else
        ExecuteFromCFGNode_s336(s52, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 94
    * Starting at 0x676
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x676 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 337
    * Segment Id for this node is: 95
    * Starting at 0x67d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
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
      assert s21.Peek(6) == 0x48c;
      assert s21.Peek(8) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x06a1);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1125);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s338(s28, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 233
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x6a1

    requires s0.stack[6] == 0x48c

    requires s0.stack[8] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1135);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s340(s10, gas - 1)
      else
        ExecuteFromCFGNode_s339(s10, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 234
    * Starting at 0x1132
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x6a1

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

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

  /** Node 340
    * Segment Id for this node is: 235
    * Starting at 0x1135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x6a1

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0cbd);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0cdf);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s7, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 151
    * Starting at 0xcdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x6a1

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x048c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s8, gas - 1)
      else
        ExecuteFromCFGNode_s342(s8, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 152
    * Starting at 0xce9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x6a1

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

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

  /** Node 343
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x6a1

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s3, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x6a1

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s7, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 96
    * Starting at 0x6a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x48c

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x06df);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s347(s3, gas - 1)
      else
        ExecuteFromCFGNode_s346(s3, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 97
    * Starting at 0x6a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(6) == 0x48c;
      assert s11.Peek(8) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0f);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 15, 0x151c985b9cd9995c8819985a5b1959);
      var s19 := Push1(s18, 0x8a);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0x48c;
      assert s21.Peek(8) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0501);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s28, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 98
    * Starting at 0x6df
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x48c

    requires s0.stack[5] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Address(s10);
      assert s11.Peek(5) == 0x48c;
      assert s11.Peek(7) == 0x137;
      var s12 := Push1(s11, 0xc0);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := CallValue(s15);
      var s17 := IsZero(s16);
      var s18 := Swap1(s17);
      var s19 := Push0(s18);
      var s20 := Swap1(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(7) == 0x48c;
      assert s21.Peek(9) == 0x137;
      var s22 := Push1(s21, 0xe0);
      var s23 := Dup2(s22);
      var s24 := Add(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Dup2(s27);
      var s29 := Dup4(s28);
      var s30 := Sub(s29);
      var s31 := Sub(s30);
      assert s31.Peek(10) == 0x48c;
      assert s31.Peek(12) == 0x137;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MStore(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Dup5(s40);
      assert s41.Peek(8) == 0x48c;
      assert s41.Peek(10) == 0x137;
      var s42 := Dup7(s41);
      var s43 := Push1(s42, 0x40);
      var s44 := MLoad(s43);
      var s45 := Push1(s44, 0x20);
      var s46 := Add(s45);
      var s47 := Push2(s46, 0x0733);
      var s48 := Swap3(s47);
      var s49 := Swap2(s48);
      var s50 := Swap1(s49);
      var s51 := Swap2(s50);
      assert s51.Peek(3) == 0x733;
      assert s51.Peek(11) == 0x48c;
      assert s51.Peek(13) == 0x137;
      var s52 := Dup3(s51);
      var s53 := MStore(s52);
      var s54 := Push1(s53, 0x01);
      var s55 := Push1(s54, 0x01);
      var s56 := Push1(s55, 0xa0);
      var s57 := Shl(s56);
      var s58 := Sub(s57);
      var s59 := And(s58);
      var s60 := Push1(s59, 0x20);
      var s61 := Dup3(s60);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s348(s61, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 99
    * Starting at 0x72c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x733

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s349(s6, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 100
    * Starting at 0x733
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x733 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Dup2(s6);
      var s8 := Dup5(s7);
      var s9 := Sub(s8);
      var s10 := Add(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := MStore(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push0(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(9) == 0x48c;
      assert s21.Peek(11) == 0x137;
      var s22 := MLoad(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup3(s24);
      var s26 := MStore(s25);
      var s27 := Dup1(s26);
      var s28 := Push1(s27, 0x20);
      var s29 := Mul(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(10) == 0x48c;
      assert s31.Peek(12) == 0x137;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := Push1(s33, 0x40);
      var s35 := MStore(s34);
      var s36 := Dup1(s35);
      var s37 := IsZero(s36);
      var s38 := Push2(s37, 0x078d);
      var s39 := JumpI(s38);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s38.stack[1] > 0 then
        ExecuteFromCFGNode_s353(s39, gas - 1)
      else
        ExecuteFromCFGNode_s350(s39, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 101
    * Starting at 0x763
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x763 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s351(s3, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 102
    * Starting at 0x767
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x767 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push0(s10);
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := Dup1(s11);
      var s13 := Dup3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(11) == 0x48c;
      assert s21.Peek(13) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap1(s24);
      var s26 := Sub(s25);
      var s27 := Swap1(s26);
      var s28 := Dup2(s27);
      var s29 := Push2(s28, 0x0767);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s351(s30, gas - 1)
      else
        ExecuteFromCFGNode_s352(s30, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 103
    * Starting at 0x78b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s353(s2, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 104
    * Starting at 0x78d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x079e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s433(s9, gas - 1)
      else
        ExecuteFromCFGNode_s354(s9, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 105
    * Starting at 0x799
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Push2(s1, 0x07c0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s3, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 107
    * Starting at 0x7c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
      var s12 := Push2(s11, 0x07e8);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := Push3(s20, 0x011170);
      assert s21.Peek(3) == 0x7e8;
      assert s21.Peek(11) == 0x48c;
      assert s21.Peek(13) == 0x137;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Pop(s23);
      var s25 := Push2(s24, 0x05d0);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s26, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 92
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x7e8

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Dup1(s7);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(5) == 0x7e8;
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup5(s17);
      var s19 := Sub(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(5) == 0x7e8;
      assert s21.Peek(13) == 0x48c;
      assert s21.Peek(15) == 0x137;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x44);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x7e8;
      assert s31.Peek(10) == 0x48c;
      assert s31.Peek(12) == 0x137;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Dup1(s33);
      var s35 := MLoad(s34);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0x01);
      var s38 := Push1(s37, 0xe0);
      var s39 := Shl(s38);
      var s40 := Sub(s39);
      var s41 := And(s40);
      assert s41.Peek(3) == 0x7e8;
      assert s41.Peek(11) == 0x48c;
      assert s41.Peek(13) == 0x137;
      var s42 := Push4(s41, 0x97a657c9);
      var s43 := Push1(s42, 0xe0);
      var s44 := Shl(s43);
      var s45 := Or(s44);
      var s46 := Swap1(s45);
      var s47 := MStore(s46);
      var s48 := Swap1(s47);
      var s49 := Jump(s48);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s49, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 108
    * Starting at 0x7e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push4(s5, 0x20487ded);
      var s7 := Push1(s6, 0xe0);
      var s8 := Shl(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x48c;
      assert s11.Peek(9) == 0x137;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Push0(s13);
      var s15 := Swap1(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Push32(s20, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      assert s21.Peek(9) == 0x48c;
      assert s21.Peek(11) == 0x137;
      var s22 := And(s21);
      var s23 := Swap1(s22);
      var s24 := Push4(s23, 0x20487ded);
      var s25 := Swap1(s24);
      var s26 := Push2(s25, 0x083d);
      var s27 := Swap1(s26);
      var s28 := Dup10(s27);
      var s29 := Swap1(s28);
      var s30 := Dup7(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(3) == 0x83d;
      assert s31.Peek(12) == 0x48c;
      assert s31.Peek(14) == 0x137;
      var s32 := Push1(s31, 0x04);
      var s33 := Add(s32);
      var s34 := Push2(s33, 0x0e03);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s35, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 178
    * Starting at 0xe03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x83d

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x83d;
      assert s11.Peek(16) == 0x48c;
      assert s11.Peek(18) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup5(s18);
      var s20 := MLoad(s19);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(8) == 0x83d;
      assert s21.Peek(17) == 0x48c;
      assert s21.Peek(19) == 0x137;
      var s22 := Dup4(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0e2e);
      var s27 := Push1(s26, 0xe0);
      var s28 := Dup7(s27);
      var s29 := Add(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0dc0);
      assert s31.Peek(0) == 0xdc0;
      assert s31.Peek(3) == 0xe2e;
      assert s31.Peek(11) == 0x83d;
      assert s31.Peek(20) == 0x48c;
      assert s31.Peek(22) == 0x137;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s32, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xe2e

    requires s0.stack[10] == 0x83d

    requires s0.stack[19] == 0x48c

    requires s0.stack[21] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s360(s8, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s362(s7, gas - 1)
      else
        ExecuteFromCFGNode_s361(s7, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe2e;
      assert s11.Peek(17) == 0x83d;
      assert s11.Peek(26) == 0x48c;
      assert s11.Peek(28) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s16, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe2e;
      assert s11.Peek(14) == 0x83d;
      assert s11.Peek(23) == 0x48c;
      assert s11.Peek(25) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe2e;
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x48c;
      assert s21.Peek(23) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s27, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 179
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x83d

    requires s0.stack[17] == 0x48c

    requires s0.stack[19] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x3f);
      var s9 := Not(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(11) == 0x83d;
      assert s11.Peek(20) == 0x48c;
      assert s11.Peek(22) == 0x137;
      var s12 := Dup5(s11);
      var s13 := Sub(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push2(s18, 0x0e4b);
      var s20 := Dup4(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(2) == 0xe4b;
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x48c;
      assert s21.Peek(23) == 0x137;
      var s22 := Push2(s21, 0x0dc0);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s364(s23, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xe4b

    requires s0.stack[12] == 0x83d

    requires s0.stack[21] == 0x48c

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s365(s8, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x83d

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s7, gas - 1)
      else
        ExecuteFromCFGNode_s366(s7, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x83d

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe4b;
      assert s11.Peek(19) == 0x83d;
      assert s11.Peek(28) == 0x48c;
      assert s11.Peek(30) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s16, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x83d

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe4b;
      assert s11.Peek(16) == 0x83d;
      assert s11.Peek(25) == 0x48c;
      assert s11.Peek(27) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe4b;
      assert s21.Peek(14) == 0x83d;
      assert s21.Peek(23) == 0x48c;
      assert s21.Peek(25) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s27, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 180
    * Starting at 0xe4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[10] == 0x83d

    requires s0.stack[19] == 0x48c

    requires s0.stack[21] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup9(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x80);
      assert s11.Peek(13) == 0x83d;
      assert s11.Peek(22) == 0x48c;
      assert s11.Peek(24) == 0x137;
      var s12 := Dup11(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(13) == 0x83d;
      assert s21.Peek(22) == 0x48c;
      assert s21.Peek(24) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Push0(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s369(s31, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 181
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x48c

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e9d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s371(s7, gas - 1)
      else
        ExecuteFromCFGNode_s370(s7, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 182
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x48c

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(14) == 0x83d;
      assert s11.Peek(23) == 0x48c;
      assert s11.Peek(25) == 0x137;
      var s12 := MStore(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Dup7(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x48c;
      assert s21.Peek(23) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap4(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap4(s24);
      var s26 := Swap1(s25);
      var s27 := Swap4(s26);
      var s28 := Add(s27);
      var s29 := Swap3(s28);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(12) == 0x83d;
      assert s31.Peek(21) == 0x48c;
      assert s31.Peek(23) == 0x137;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0e6b);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s35, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 183
    * Starting at 0xe9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x48c

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup10(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(12) == 0x83d;
      assert s11.Peek(21) == 0x48c;
      assert s11.Peek(23) == 0x137;
      var s12 := And(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x80);
      var s18 := Dup10(s17);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup9(s20);
      assert s21.Peek(12) == 0x83d;
      assert s21.Peek(21) == 0x48c;
      assert s21.Peek(23) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Sub(s22);
      var s24 := Dup4(s23);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup11(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Swap6(s29);
      var s31 := Pop(s30);
      assert s31.Peek(10) == 0x83d;
      assert s31.Peek(19) == 0x48c;
      assert s31.Peek(21) == 0x137;
      var s32 := Push2(s31, 0x0ecc);
      var s33 := Dup2(s32);
      var s34 := Dup8(s33);
      var s35 := Push2(s34, 0x0dc0);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s36, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0xecc

    requires s0.stack[13] == 0x83d

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s373(s8, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x83d

    requires s0.stack[25] == 0x48c

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s375(s7, gas - 1)
      else
        ExecuteFromCFGNode_s374(s7, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x83d

    requires s0.stack[25] == 0x48c

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xecc;
      assert s11.Peek(20) == 0x83d;
      assert s11.Peek(29) == 0x48c;
      assert s11.Peek(31) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s16, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x83d

    requires s0.stack[25] == 0x48c

    requires s0.stack[27] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xecc;
      assert s11.Peek(17) == 0x83d;
      assert s11.Peek(26) == 0x48c;
      assert s11.Peek(28) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xecc;
      assert s21.Peek(15) == 0x83d;
      assert s21.Peek(24) == 0x48c;
      assert s21.Peek(26) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s27, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 184
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[11] == 0x83d

    requires s0.stack[20] == 0x48c

    requires s0.stack[22] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x83d;
      assert s11.Peek(12) == 0x48c;
      assert s11.Peek(14) == 0x137;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s14, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 109
    * Starting at 0x83d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(10) == 0x48c;
      assert s11.Peek(12) == 0x137;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0858);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s16, gas - 1)
      else
        ExecuteFromCFGNode_s378(s16, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 110
    * Starting at 0x851
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x851 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 379
    * Segment Id for this node is: 111
    * Starting at 0x858
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x858 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(10) == 0x48c;
      assert s11.Peek(12) == 0x137;
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
      assert s21.Peek(9) == 0x48c;
      assert s21.Peek(11) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x087c);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0eda);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s28, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 185
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x87c

    requires s0.stack[9] == 0x48c

    requires s0.stack[11] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0eea);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s382(s10, gas - 1)
      else
        ExecuteFromCFGNode_s381(s10, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 186
    * Starting at 0xee7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x87c

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

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

  /** Node 382
    * Segment Id for this node is: 187
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x87c

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s7, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 112
    * Starting at 0x87c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push0(s3);
      var s5 := Dup4(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x091f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s422(s8, gas - 1)
      else
        ExecuteFromCFGNode_s384(s8, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 113
    * Starting at 0x886
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x886 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x23b872dd);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(10) == 0x48c;
      assert s11.Peek(12) == 0x137;
      var s12 := MStore(s11);
      var s13 := Address(s12);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup2(s18);
      var s20 := Add(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x48c;
      assert s21.Peek(12) == 0x137;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Push32(s23, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(9) == 0x48c;
      assert s31.Peek(11) == 0x137;
      var s32 := Push4(s31, 0x23b872dd);
      var s33 := Swap1(s32);
      var s34 := Push1(s33, 0x64);
      var s35 := Add(s34);
      var s36 := Push1(s35, 0x20);
      var s37 := Push1(s36, 0x40);
      var s38 := MLoad(s37);
      var s39 := Dup1(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      assert s41.Peek(13) == 0x48c;
      assert s41.Peek(15) == 0x137;
      var s42 := Dup2(s41);
      var s43 := Push0(s42);
      var s44 := Dup8(s43);
      var s45 := Gas(s44);
      var s46 := Call(s45);
      var s47 := IsZero(s46);
      var s48 := Dup1(s47);
      var s49 := IsZero(s48);
      var s50 := Push2(s49, 0x08f5);
      var s51 := JumpI(s50);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s50.stack[1] > 0 then
        ExecuteFromCFGNode_s386(s51, gas - 1)
      else
        ExecuteFromCFGNode_s385(s51, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 114
    * Starting at 0x8ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 386
    * Segment Id for this node is: 115
    * Starting at 0x8f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(11) == 0x48c;
      assert s11.Peek(13) == 0x137;
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
      assert s21.Peek(10) == 0x48c;
      assert s21.Peek(12) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0919);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1125);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s28, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 233
    * Starting at 0x1125
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1125 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x919

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1135);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s389(s10, gas - 1)
      else
        ExecuteFromCFGNode_s388(s10, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 234
    * Starting at 0x1132
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x919

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

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

  /** Node 389
    * Segment Id for this node is: 235
    * Starting at 0x1135
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x919

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0cbd);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0cdf);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s390(s7, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 151
    * Starting at 0xcdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x919

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x048c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s392(s8, gas - 1)
      else
        ExecuteFromCFGNode_s391(s8, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 152
    * Starting at 0xce9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x919

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

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

  /** Node 392
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0xcbd

    requires s0.stack[6] == 0x919

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s3, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x919

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s394(s7, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 116
    * Starting at 0x919
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x919 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x09a2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s395(s4, gas - 1)
  }

  /** Node 395
    * Segment Id for this node is: 124
    * Starting at 0x9a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x96f4e9f9);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(11) == 0x48c;
      assert s11.Peek(13) == 0x137;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := Push32(s13, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Push4(s16, 0x96f4e9f9);
      var s18 := Swap1(s17);
      var s19 := Dup4(s18);
      var s20 := Swap1(s19);
      var s21 := Push2(s20, 0x09f2);
      assert s21.Peek(0) == 0x9f2;
      assert s21.Peek(12) == 0x48c;
      assert s21.Peek(14) == 0x137;
      var s22 := Swap1(s21);
      var s23 := Dup12(s22);
      var s24 := Swap1(s23);
      var s25 := Dup9(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0e03);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s30, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 178
    * Starting at 0xe03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x9f2

    requires s0.stack[14] == 0x48c

    requires s0.stack[16] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x9f2;
      assert s11.Peek(18) == 0x48c;
      assert s11.Peek(20) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup5(s18);
      var s20 := MLoad(s19);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(8) == 0x9f2;
      assert s21.Peek(19) == 0x48c;
      assert s21.Peek(21) == 0x137;
      var s22 := Dup4(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0e2e);
      var s27 := Push1(s26, 0xe0);
      var s28 := Dup7(s27);
      var s29 := Add(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0dc0);
      assert s31.Peek(0) == 0xdc0;
      assert s31.Peek(3) == 0xe2e;
      assert s31.Peek(11) == 0x9f2;
      assert s31.Peek(22) == 0x48c;
      assert s31.Peek(24) == 0x137;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s397(s32, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0xe2e

    requires s0.stack[10] == 0x9f2

    requires s0.stack[21] == 0x48c

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s398(s8, gas - 1)
  }

  /** Node 398
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s400(s7, gas - 1)
      else
        ExecuteFromCFGNode_s399(s7, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe2e;
      assert s11.Peek(17) == 0x9f2;
      assert s11.Peek(28) == 0x48c;
      assert s11.Peek(30) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s398(s16, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe2e;
      assert s11.Peek(14) == 0x9f2;
      assert s11.Peek(25) == 0x48c;
      assert s11.Peek(27) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe2e;
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x48c;
      assert s21.Peek(25) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s27, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 179
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[8] == 0x9f2

    requires s0.stack[19] == 0x48c

    requires s0.stack[21] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x3f);
      var s9 := Not(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(11) == 0x9f2;
      assert s11.Peek(22) == 0x48c;
      assert s11.Peek(24) == 0x137;
      var s12 := Dup5(s11);
      var s13 := Sub(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push2(s18, 0x0e4b);
      var s20 := Dup4(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(2) == 0xe4b;
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x48c;
      assert s21.Peek(25) == 0x137;
      var s22 := Push2(s21, 0x0dc0);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s402(s23, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0xe4b

    requires s0.stack[12] == 0x9f2

    requires s0.stack[23] == 0x48c

    requires s0.stack[25] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s403(s8, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x9f2

    requires s0.stack[26] == 0x48c

    requires s0.stack[28] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s405(s7, gas - 1)
      else
        ExecuteFromCFGNode_s404(s7, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x9f2

    requires s0.stack[26] == 0x48c

    requires s0.stack[28] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe4b;
      assert s11.Peek(19) == 0x9f2;
      assert s11.Peek(30) == 0x48c;
      assert s11.Peek(32) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s16, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x9f2

    requires s0.stack[26] == 0x48c

    requires s0.stack[28] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe4b;
      assert s11.Peek(16) == 0x9f2;
      assert s11.Peek(27) == 0x48c;
      assert s11.Peek(29) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe4b;
      assert s21.Peek(14) == 0x9f2;
      assert s21.Peek(25) == 0x48c;
      assert s21.Peek(27) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s27, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 180
    * Starting at 0xe4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[10] == 0x9f2

    requires s0.stack[21] == 0x48c

    requires s0.stack[23] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup9(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x80);
      assert s11.Peek(13) == 0x9f2;
      assert s11.Peek(24) == 0x48c;
      assert s11.Peek(26) == 0x137;
      var s12 := Dup11(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(13) == 0x9f2;
      assert s21.Peek(24) == 0x48c;
      assert s21.Peek(26) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Push0(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s407(s31, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 181
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e9d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s409(s7, gas - 1)
      else
        ExecuteFromCFGNode_s408(s7, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 182
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(14) == 0x9f2;
      assert s11.Peek(25) == 0x48c;
      assert s11.Peek(27) == 0x137;
      var s12 := MStore(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Dup7(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x48c;
      assert s21.Peek(25) == 0x137;
      var s22 := Add(s21);
      var s23 := Swap4(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap4(s24);
      var s26 := Swap1(s25);
      var s27 := Swap4(s26);
      var s28 := Add(s27);
      var s29 := Swap3(s28);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(12) == 0x9f2;
      assert s31.Peek(23) == 0x48c;
      assert s31.Peek(25) == 0x137;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0e6b);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s407(s35, gas - 1)
  }

  /** Node 409
    * Segment Id for this node is: 183
    * Starting at 0xe9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup10(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(12) == 0x9f2;
      assert s11.Peek(23) == 0x48c;
      assert s11.Peek(25) == 0x137;
      var s12 := And(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x80);
      var s18 := Dup10(s17);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup9(s20);
      assert s21.Peek(12) == 0x9f2;
      assert s21.Peek(23) == 0x48c;
      assert s21.Peek(25) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Sub(s22);
      var s24 := Dup4(s23);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup11(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Swap6(s29);
      var s31 := Pop(s30);
      assert s31.Peek(10) == 0x9f2;
      assert s31.Peek(21) == 0x48c;
      assert s31.Peek(23) == 0x137;
      var s32 := Push2(s31, 0x0ecc);
      var s33 := Dup2(s32);
      var s34 := Dup8(s33);
      var s35 := Push2(s34, 0x0dc0);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s410(s36, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[2] == 0xecc

    requires s0.stack[13] == 0x9f2

    requires s0.stack[24] == 0x48c

    requires s0.stack[26] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s411(s8, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x9f2

    requires s0.stack[27] == 0x48c

    requires s0.stack[29] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s413(s7, gas - 1)
      else
        ExecuteFromCFGNode_s412(s7, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x9f2

    requires s0.stack[27] == 0x48c

    requires s0.stack[29] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xecc;
      assert s11.Peek(20) == 0x9f2;
      assert s11.Peek(31) == 0x48c;
      assert s11.Peek(33) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s411(s16, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x9f2

    requires s0.stack[27] == 0x48c

    requires s0.stack[29] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xecc;
      assert s11.Peek(17) == 0x9f2;
      assert s11.Peek(28) == 0x48c;
      assert s11.Peek(30) == 0x137;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xecc;
      assert s21.Peek(15) == 0x9f2;
      assert s21.Peek(26) == 0x48c;
      assert s21.Peek(28) == 0x137;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s27, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 184
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[11] == 0x9f2

    requires s0.stack[22] == 0x48c

    requires s0.stack[24] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x9f2;
      assert s11.Peek(14) == 0x48c;
      assert s11.Peek(16) == 0x137;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s14, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 125
    * Starting at 0x9f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Dup9(s9);
      var s11 := Gas(s10);
      assert s11.Peek(18) == 0x48c;
      assert s11.Peek(20) == 0x137;
      var s12 := Call(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0a0e);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s417(s17, gas - 1)
      else
        ExecuteFromCFGNode_s416(s17, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 126
    * Starting at 0xa07
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa07 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 417
    * Segment Id for this node is: 127
    * Starting at 0xa0e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := ReturnDataSize(s8);
      var s10 := Push1(s9, 0x1f);
      var s11 := Not(s10);
      assert s11.Peek(10) == 0x48c;
      assert s11.Peek(12) == 0x137;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(9) == 0x48c;
      assert s21.Peek(11) == 0x137;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x0a33);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0eda);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s418(s29, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 185
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xa33

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0eea);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s420(s10, gas - 1)
      else
        ExecuteFromCFGNode_s419(s10, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 186
    * Starting at 0xee7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa33

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

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

  /** Node 420
    * Segment Id for this node is: 187
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xa33

    requires s0.stack[11] == 0x48c

    requires s0.stack[13] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s7, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 128
    * Starting at 0xa33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0xf105803bee01dee7039d5715e807acca02889381ddf6041ddc55af0c68b4fc86);
      var s5 := Swap1(s4);
      var s6 := Push0(s5);
      var s7 := Swap1(s6);
      var s8 := Log2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(4) == 0x48c;
      assert s11.Peek(6) == 0x137;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s16, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 117
    * Starting at 0x91f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Dup1(s4);
      var s6 := CallValue(s5);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0965);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s425(s10, gas - 1)
      else
        ExecuteFromCFGNode_s423(s10, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 118
    * Starting at 0x92b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
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
      assert s11.Peek(10) == 0x48c;
      assert s11.Peek(12) == 0x137;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x10);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 16, 0x696e73756666696369656e7420666565);
      var s19 := Push1(s18, 0x80);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(10) == 0x48c;
      assert s21.Peek(12) == 0x137;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x0501);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s424(s28, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 83
    * Starting at 0x501
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

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
      var s8 := Revert(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 425
    * Segment Id for this node is: 119
    * Starting at 0x965
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x965 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallValue(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x09a2);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s7, gas - 1)
      else
        ExecuteFromCFGNode_s426(s7, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 120
    * Starting at 0x96e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := Push2(s1, 0x08fc);
      var s3 := Push2(s2, 0x097b);
      var s4 := Dup4(s3);
      var s5 := CallValue(s4);
      var s6 := Push2(s5, 0x1140);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s7, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 236
    * Starting at 0x1140
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1140 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x97b

    requires s0.stack[12] == 0x48c

    requires s0.stack[14] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x02cc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s10, gas - 1)
      else
        ExecuteFromCFGNode_s428(s10, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 237
    * Starting at 0x114c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x97b

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push0(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 429
    * Segment Id for this node is: 64
    * Starting at 0x2cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x97b

    requires s0.stack[13] == 0x48c

    requires s0.stack[15] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s430(s6, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 121
    * Starting at 0x97b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x48c

    requires s0.stack[12] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := IsZero(s4);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Mul(s7);
      var s9 := Swap2(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(13) == 0x48c;
      assert s11.Peek(15) == 0x137;
      var s12 := Dup2(s11);
      var s13 := Dup2(s12);
      var s14 := Dup6(s13);
      var s15 := Dup9(s14);
      var s16 := Dup9(s15);
      var s17 := Call(s16);
      var s18 := Swap4(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(9) == 0x48c;
      assert s21.Peek(11) == 0x137;
      var s22 := Pop(s21);
      var s23 := IsZero(s22);
      var s24 := Dup1(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x09a0);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s432(s27, gas - 1)
      else
        ExecuteFromCFGNode_s431(s27, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 122
    * Starting at 0x999
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x999 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 432
    * Segment Id for this node is: 123
    * Starting at 0x9a0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x48c

    requires s0.stack[10] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s395(s2, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 106
    * Starting at 0x79e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x48c

    requires s0.stack[9] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push32(s1, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s355(s2, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 30
    * Starting at 0x124
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0137);
      var s3 := Push2(s2, 0x0132);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0d21);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s7, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 158
    * Starting at 0xd21
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd21 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x132

    requires s0.stack[3] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0d31);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s437(s10, gas - 1)
      else
        ExecuteFromCFGNode_s436(s10, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 159
    * Starting at 0xd2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x132

    requires s0.stack[4] == 0x137

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

  /** Node 437
    * Segment Id for this node is: 160
    * Starting at 0xd31
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd31 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x132

    requires s0.stack[4] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s438(s7, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 31
    * Starting at 0x132
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0461);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s3, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 78
    * Starting at 0x461
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x461 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x048c);
      var s3 := Push32(s2, 0x0000000000000000000000000000000000000000000000009d70576d8e253bcf);
      var s4 := Caller(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x060d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s335(s7, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 25
    * Starting at 0xf7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7 as nat
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
      var s5 := Push2(s4, 0x0102);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s442(s6, gas - 1)
      else
        ExecuteFromCFGNode_s441(s6, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 26
    * Starting at 0xff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff as nat
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

  /** Node 442
    * Segment Id for this node is: 27
    * Starting at 0x102
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0116);
      var s4 := Push2(s3, 0x0111);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0cec);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s8, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 153
    * Starting at 0xcec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0cfd);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s445(s11, gas - 1)
      else
        ExecuteFromCFGNode_s444(s11, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 154
    * Starting at 0xcfa
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

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

  /** Node 445
    * Segment Id for this node is: 155
    * Starting at 0xcfd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcfd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0d06);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0cc4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s5, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 148
    * Starting at 0xcc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xd06

    requires s0.stack[6] == 0x111

    requires s0.stack[7] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0xd06;
      assert s11.Peek(9) == 0x111;
      assert s11.Peek(10) == 0x116;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0cda);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s448(s14, gas - 1)
      else
        ExecuteFromCFGNode_s447(s14, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 149
    * Starting at 0xcd7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd06

    requires s0.stack[7] == 0x111

    requires s0.stack[8] == 0x116

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

  /** Node 448
    * Segment Id for this node is: 150
    * Starting at 0xcda
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xd06

    requires s0.stack[7] == 0x111

    requires s0.stack[8] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s449(s5, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 156
    * Starting at 0xd06
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd06 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x111

    requires s0.stack[6] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0d16);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0cdf);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s11, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 151
    * Starting at 0xcdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd16

    requires s0.stack[7] == 0x111

    requires s0.stack[8] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x048c);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s452(s8, gas - 1)
      else
        ExecuteFromCFGNode_s451(s8, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 152
    * Starting at 0xce9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd16

    requires s0.stack[7] == 0x111

    requires s0.stack[8] == 0x116

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

  /** Node 452
    * Segment Id for this node is: 79
    * Starting at 0x48c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xd16

    requires s0.stack[7] == 0x111

    requires s0.stack[8] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s3, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 157
    * Starting at 0xd16
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x111

    requires s0.stack[6] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      ExecuteFromCFGNode_s454(s11, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 28
    * Starting at 0x111
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x02d2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s3, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 65
    * Starting at 0x2d2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := Address(s9);
      var s11 := Push1(s10, 0xc0);
      assert s11.Peek(6) == 0x116;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Dup3(s14);
      var s16 := Swap1(s15);
      var s17 := MStore(s16);
      var s18 := Dup4(s17);
      var s19 := MLoad(s18);
      var s20 := Dup1(s19);
      var s21 := Dup5(s20);
      assert s21.Peek(9) == 0x116;
      var s22 := Sub(s21);
      var s23 := Swap1(s22);
      var s24 := Swap2(s23);
      var s25 := Add(s24);
      var s26 := Dup2(s25);
      var s27 := MStore(s26);
      var s28 := Push1(s27, 0xe0);
      var s29 := Dup4(s28);
      var s30 := Add(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(8) == 0x116;
      var s32 := MStore(s31);
      var s33 := Dup3(s32);
      var s34 := MStore(s33);
      var s35 := Dup3(s34);
      var s36 := MLoad(s35);
      var s37 := PushN(s36, 9, 0x056bc75e2d63100001);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup1(s38);
      var s40 := Dup4(s39);
      var s41 := Add(s40);
      assert s41.Peek(9) == 0x116;
      var s42 := Dup3(s41);
      var s43 := Swap1(s42);
      var s44 := MStore(s43);
      var s45 := Dup3(s44);
      var s46 := Dup7(s45);
      var s47 := Add(s46);
      var s48 := Dup5(s47);
      var s49 := Swap1(s48);
      var s50 := MStore(s49);
      var s51 := Dup6(s50);
      assert s51.Peek(9) == 0x116;
      var s52 := MLoad(s51);
      var s53 := Dup1(s52);
      var s54 := Dup5(s53);
      var s55 := Sub(s54);
      var s56 := Dup8(s55);
      var s57 := Add(s56);
      var s58 := Dup2(s57);
      var s59 := MStore(s58);
      var s60 := Push1(s59, 0x60);
      var s61 := Swap1(s60);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s456(s61, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 66
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      var s2 := Add(s1);
      var s3 := Dup7(s2);
      var s4 := MStore(s3);
      var s5 := Dup1(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(7) == 0x116;
      var s12 := Dup5(s11);
      var s13 := MLoad(s12);
      var s14 := Push0(s13);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := Swap3(s17);
      var s19 := Dup2(s18);
      var s20 := Add(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(10) == 0x116;
      var s22 := MStore(s21);
      var s23 := Swap2(s22);
      var s24 := Swap5(s23);
      var s25 := Swap1(s24);
      var s26 := Swap4(s25);
      var s27 := Dup6(s26);
      var s28 := Swap3(s27);
      var s29 := Swap1(s28);
      var s30 := Swap2(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(10) == 0x116;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Dup4(s33);
      var s35 := Push2(s34, 0x036a);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s457(s36, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 69
    * Starting at 0x36a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Dup7(s6);
      var s8 := Push2(s7, 0x037b);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s488(s9, gas - 1)
      else
        ExecuteFromCFGNode_s458(s9, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 70
    * Starting at 0x376
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Push2(s1, 0x039d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s3, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 72
    * Starting at 0x39d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(8) == 0x116;
      var s12 := Push2(s11, 0x03c5);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := Push3(s20, 0x011170);
      assert s21.Peek(3) == 0x3c5;
      assert s21.Peek(12) == 0x116;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Pop(s23);
      var s25 := Push2(s24, 0x05d0);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s26, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 92
    * Starting at 0x5d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x3c5

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Dup1(s7);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(5) == 0x3c5;
      assert s11.Peek(14) == 0x116;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup5(s17);
      var s19 := Sub(s18);
      var s20 := Swap1(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(5) == 0x3c5;
      assert s21.Peek(14) == 0x116;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x44);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(2) == 0x3c5;
      assert s31.Peek(11) == 0x116;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Dup1(s33);
      var s35 := MLoad(s34);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0x01);
      var s38 := Push1(s37, 0xe0);
      var s39 := Shl(s38);
      var s40 := Sub(s39);
      var s41 := And(s40);
      assert s41.Peek(3) == 0x3c5;
      assert s41.Peek(12) == 0x116;
      var s42 := Push4(s41, 0x97a657c9);
      var s43 := Push1(s42, 0xe0);
      var s44 := Shl(s43);
      var s45 := Or(s44);
      var s46 := Swap1(s45);
      var s47 := MStore(s46);
      var s48 := Swap1(s47);
      var s49 := Jump(s48);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s49, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 73
    * Starting at 0x3c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push4(s5, 0x20487ded);
      var s7 := Push1(s6, 0xe0);
      var s8 := Shl(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x116;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0xa0);
      var s17 := Shl(s16);
      var s18 := Sub(s17);
      var s19 := Push32(s18, 0x00000000000000000000000080226fc0ee2b096224eeac085bb9a8cba1146f7d);
      var s20 := And(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(8) == 0x116;
      var s22 := Push4(s21, 0x20487ded);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0418);
      var s25 := Swap1(s24);
      var s26 := Dup10(s25);
      var s27 := Swap1(s26);
      var s28 := Dup6(s27);
      var s29 := Swap1(s28);
      var s30 := Push1(s29, 0x04);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x418;
      assert s31.Peek(12) == 0x116;
      var s32 := Push2(s31, 0x0e03);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s33, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 178
    * Starting at 0xe03
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x418

    requires s0.stack[12] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x40);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup6(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x418;
      assert s11.Peek(16) == 0x116;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Dup2(s13);
      var s15 := Dup2(s14);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup5(s18);
      var s20 := MLoad(s19);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(8) == 0x418;
      assert s21.Peek(17) == 0x116;
      var s22 := Dup4(s21);
      var s23 := Dup7(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push2(s25, 0x0e2e);
      var s27 := Push1(s26, 0xe0);
      var s28 := Dup7(s27);
      var s29 := Add(s28);
      var s30 := Dup3(s29);
      var s31 := Push2(s30, 0x0dc0);
      assert s31.Peek(0) == 0xdc0;
      assert s31.Peek(3) == 0xe2e;
      assert s31.Peek(11) == 0x418;
      assert s31.Peek(20) == 0x116;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s463(s32, gas - 1)
  }

  /** Node 463
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0xe2e

    requires s0.stack[10] == 0x418

    requires s0.stack[19] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s464(s8, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s7, gas - 1)
      else
        ExecuteFromCFGNode_s465(s7, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe2e;
      assert s11.Peek(17) == 0x418;
      assert s11.Peek(26) == 0x116;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s16, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0xe2e

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe2e;
      assert s11.Peek(14) == 0x418;
      assert s11.Peek(23) == 0x116;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe2e;
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x116;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s27, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 179
    * Starting at 0xe2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x418

    requires s0.stack[17] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x3f);
      var s9 := Not(s8);
      var s10 := Dup1(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(11) == 0x418;
      assert s11.Peek(20) == 0x116;
      var s12 := Dup5(s11);
      var s13 := Sub(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push2(s18, 0x0e4b);
      var s20 := Dup4(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(2) == 0xe4b;
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x116;
      var s22 := Push2(s21, 0x0dc0);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s468(s23, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xe4b

    requires s0.stack[12] == 0x418

    requires s0.stack[21] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s469(s8, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x418

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s471(s7, gas - 1)
      else
        ExecuteFromCFGNode_s470(s7, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x418

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xe4b;
      assert s11.Peek(19) == 0x418;
      assert s11.Peek(28) == 0x116;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s16, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0xe4b

    requires s0.stack[15] == 0x418

    requires s0.stack[24] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xe4b;
      assert s11.Peek(16) == 0x418;
      assert s11.Peek(25) == 0x116;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xe4b;
      assert s21.Peek(14) == 0x418;
      assert s21.Peek(23) == 0x116;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s27, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 180
    * Starting at 0xe4b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[10] == 0x418

    requires s0.stack[19] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup9(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x80);
      assert s11.Peek(13) == 0x418;
      assert s11.Peek(22) == 0x116;
      var s12 := Dup11(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := MLoad(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := MStore(s18);
      var s20 := Swap1(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(13) == 0x418;
      assert s21.Peek(22) == 0x116;
      var s22 := Add(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Push0(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := Add(s29);
      var s31 := Swap1(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s473(s31, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 181
    * Starting at 0xe6b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0e9d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s475(s7, gas - 1)
      else
        ExecuteFromCFGNode_s474(s7, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 182
    * Starting at 0xe74
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup5(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(14) == 0x418;
      assert s11.Peek(23) == 0x116;
      var s12 := MStore(s11);
      var s13 := Dup7(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Dup7(s15);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Swap4(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x116;
      var s22 := Add(s21);
      var s23 := Swap4(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Swap4(s24);
      var s26 := Swap1(s25);
      var s27 := Swap4(s26);
      var s28 := Add(s27);
      var s29 := Swap3(s28);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(12) == 0x418;
      assert s31.Peek(21) == 0x116;
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0e6b);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s35, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 183
    * Starting at 0xe9d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup10(s3);
      var s5 := Add(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(12) == 0x418;
      assert s11.Peek(21) == 0x116;
      var s12 := And(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup10(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x80);
      var s18 := Dup10(s17);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup9(s20);
      assert s21.Peek(12) == 0x418;
      assert s21.Peek(21) == 0x116;
      var s22 := Dup3(s21);
      var s23 := Sub(s22);
      var s24 := Dup4(s23);
      var s25 := Add(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup11(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Swap6(s29);
      var s31 := Pop(s30);
      assert s31.Peek(10) == 0x418;
      assert s31.Peek(19) == 0x116;
      var s32 := Push2(s31, 0x0ecc);
      var s33 := Dup2(s32);
      var s34 := Dup8(s33);
      var s35 := Push2(s34, 0x0dc0);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s476(s36, gas - 1)
  }

  /** Node 476
    * Segment Id for this node is: 174
    * Starting at 0xdc0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0xecc

    requires s0.stack[13] == 0x418

    requires s0.stack[22] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push0(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s477(s8, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 175
    * Starting at 0xdc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x418

    requires s0.stack[25] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0de4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s479(s7, gas - 1)
      else
        ExecuteFromCFGNode_s478(s7, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 176
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x418

    requires s0.stack[25] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0xecc;
      assert s11.Peek(20) == 0x418;
      assert s11.Peek(29) == 0x116;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0dc8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s16, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 177
    * Starting at 0xde4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0xecc

    requires s0.stack[16] == 0x418

    requires s0.stack[25] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(6) == 0xecc;
      assert s11.Peek(17) == 0x418;
      assert s11.Peek(26) == 0x116;
      var s12 := Not(s11);
      var s13 := Push1(s12, 0x1f);
      var s14 := Dup4(s13);
      var s15 := Add(s14);
      var s16 := And(s15);
      var s17 := Dup6(s16);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0xecc;
      assert s21.Peek(15) == 0x418;
      assert s21.Peek(24) == 0x116;
      var s22 := Pop(s21);
      var s23 := Swap3(s22);
      var s24 := Swap2(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s480(s27, gas - 1)
  }

  /** Node 480
    * Segment Id for this node is: 184
    * Starting at 0xecc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -11
    * Net Capacity Effect: +11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xecc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x418

    requires s0.stack[20] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 11);
      var s3 := Swap(s2, 10);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x418;
      assert s11.Peek(12) == 0x116;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s14, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 74
    * Starting at 0x418
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup7(s8);
      var s10 := Gas(s9);
      var s11 := StaticCall(s10);
      assert s11.Peek(10) == 0x116;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x0433);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s483(s16, gas - 1)
      else
        ExecuteFromCFGNode_s482(s16, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 75
    * Starting at 0x42c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 483
    * Segment Id for this node is: 76
    * Starting at 0x433
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x433 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
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
      assert s11.Peek(10) == 0x116;
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
      assert s21.Peek(9) == 0x116;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0457);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x0eda);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s484(s28, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 185
    * Starting at 0xeda
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeda as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x457

    requires s0.stack[9] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0eea);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s486(s10, gas - 1)
      else
        ExecuteFromCFGNode_s485(s10, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 186
    * Starting at 0xee7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x457

    requires s0.stack[10] == 0x116

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

  /** Node 486
    * Segment Id for this node is: 187
    * Starting at 0xeea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x457

    requires s0.stack[10] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s487(s7, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 77
    * Starting at 0x457
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap7(s1);
      var s3 := Swap6(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s10, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 71
    * Starting at 0x37b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x116

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push32(s1, 0x000000000000000000000000514910771af9ca656af840dff83e8264ecf986ca);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s459(s2, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 19
    * Starting at 0xc3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3 as nat
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
      var s5 := Push2(s4, 0x00ce);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s491(s6, gas - 1)
      else
        ExecuteFromCFGNode_s490(s6, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 20
    * Starting at 0xcb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
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

  /** Node 491
    * Segment Id for this node is: 21
    * Starting at 0xce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00e2);
      var s4 := Push2(s3, 0x00dd);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0c96);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s492(s8, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 143
    * Starting at 0xc96
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xdd

    requires s0.stack[3] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0ca6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s494(s10, gas - 1)
      else
        ExecuteFromCFGNode_s493(s10, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 144
    * Starting at 0xca3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xdd

    requires s0.stack[4] == 0xe2

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

  /** Node 494
    * Segment Id for this node is: 145
    * Starting at 0xca6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xdd

    requires s0.stack[4] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xe0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Not(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(5) == 0xdd;
      assert s11.Peek(6) == 0xe2;
      var s12 := Dup2(s11);
      var s13 := Eq(s12);
      var s14 := Push2(s13, 0x0cbd);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s496(s15, gas - 1)
      else
        ExecuteFromCFGNode_s495(s15, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 146
    * Starting at 0xcba
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xdd

    requires s0.stack[5] == 0xe2

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

  /** Node 496
    * Segment Id for this node is: 147
    * Starting at 0xcbd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xdd

    requires s0.stack[5] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s7, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 22
    * Starting at 0xdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x029c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s498(s3, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 62
    * Starting at 0x29c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Not(s7);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Push4(s10, 0x85572ffb);
      assert s11.Peek(4) == 0xe2;
      var s12 := Push1(s11, 0xe0);
      var s13 := Shl(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := Push2(s15, 0x02cc);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s500(s17, gas - 1)
      else
        ExecuteFromCFGNode_s499(s17, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 63
    * Starting at 0x2b7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Not(s6);
      var s8 := Dup3(s7);
      var s9 := And(s8);
      var s10 := Push4(s9, 0x01ffc9a7);
      var s11 := Push1(s10, 0xe0);
      assert s11.Peek(5) == 0xe2;
      var s12 := Shl(s11);
      var s13 := Eq(s12);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s500(s13, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 64
    * Starting at 0x2cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xe2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s6, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 23
    * Starting at 0xe2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2 as nat
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
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s47(s10, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 18
    * Starting at 0xbf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf as nat
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
