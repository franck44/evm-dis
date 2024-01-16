
include "/Users/franck/development/evm-dis/src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module EVMProofObject {

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
      var s1 := PushN(s0, 1, 0x04);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := PushN(s4, 2, 0x000d);
      assert s5.stack[0] == 0xd;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s5(s6, gas - 1)
      else
        ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x09df);
      assert s1.stack[0] == 0x9df;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 114
    * Starting at 0x9df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s3 := Caller(s2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x09fc);
      assert s5.stack[0] == 0x9fc;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s6, gas - 1)
      else
        ExecuteFromCFGNode_s3(s6, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 115
    * Starting at 0x9fb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fb as nat
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

  /** Node 4
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 5
    * Segment Id for this node is: 2
    * Starting at 0xd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 1, 0x1c);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 4, 0x4515cef3);
      var s9 := Dup(s8, 2);
      var s10 := Xor(s9);
      var s11 := PushN(s10, 2, 0x002b);
      assert s11.stack[0] == 0x2b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s12, gas - 1)
      else
        ExecuteFromCFGNode_s6(s12, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 3
    * Starting at 0x23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0045);
      assert s4.stack[0] == 0x45;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x45
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := CallValue(s3);
      var s5 := Xor(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s8(s7, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0xd0e30db0);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s5 := ExtCodeSize(s4);
      var s6 := IsZero(s5);
      var s7 := PushN(s6, 2, 0x09fc);
      assert s7.stack[0] == 0x9fc;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s8, gas - 1)
      else
        ExecuteFromCFGNode_s9(s8, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x73
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x011c);
      var s5 := CallValue(s4);
      var s6 := PushN(s5, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s7 := Gas(s6);
      var s8 := Call(s7);
      var s9 := PushN(s8, 2, 0x00a2);
      assert s9.stack[0] == 0xa2;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s10, gas - 1)
      else
        ExecuteFromCFGNode_s10(s10, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x98
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 11
    * Segment Id for this node is: 11
    * Starting at 0xa2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := PushN(s3, 1, 0x02);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 4);
      var s7 := MStore(s6);
      var s8 := Add(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s12(s8, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 12
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MLoad(s4);
      var s6 := Mul(s5);
      var s7 := PushN(s6, 1, 0x04);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x01da);
      assert s12.stack[0] == 0x1da;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s13, gas - 1)
      else
        ExecuteFromCFGNode_s13(s13, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 13
    * Starting at 0xc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 32, 0x23b872dd00000000000000000000000000000000000000000000000000000000);
      var s6 := PushN(s5, 2, 0x0180);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0160);
      var s9 := PushN(s8, 1, 0x04);
      var s10 := Dup(s9, 1);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Dup(s11, 5);
      var s13 := PushN(s12, 2, 0x01a0);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := Dup(s15, 3);
      var s17 := PushN(s16, 1, 0x20);
      var s18 := Dup(s17, 6);
      var s19 := Add(s18);
      var s20 := PushN(s19, 1, 0x04);
      var s21 := Gas(s20);
      var s22 := StaticCall(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Dup(s24, 1);
      var s26 := MLoad(s25);
      var s27 := Dup(s26, 3);
      var s28 := Add(s27);
      var s29 := Swap(s28, 2);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      var s32 := Caller(s31);
      var s33 := PushN(s32, 1, 0x20);
      var s34 := Dup(s33, 3);
      var s35 := PushN(s34, 2, 0x01a0);
      var s36 := Add(s35);
      var s37 := Add(s36);
      var s38 := MStore(s37);
      var s39 := PushN(s38, 1, 0x20);
      var s40 := Dup(s39, 2);
      var s41 := Add(s40);
      var s42 := Swap(s41, 1);
      var s43 := Pop(s42);
      var s44 := Address(s43);
      var s45 := PushN(s44, 1, 0x20);
      var s46 := Dup(s45, 3);
      var s47 := PushN(s46, 2, 0x01a0);
      var s48 := Add(s47);
      var s49 := Add(s48);
      var s50 := MStore(s49);
      var s51 := PushN(s50, 1, 0x20);
      var s52 := Dup(s51, 2);
      var s53 := Add(s52);
      var s54 := Swap(s53, 1);
      var s55 := Pop(s54);
      var s56 := PushN(s55, 1, 0x20);
      var s57 := PushN(s56, 2, 0x0100);
      var s58 := MLoad(s57);
      var s59 := Mul(s58);
      var s60 := PushN(s59, 1, 0x04);
      var s61 := Add(s60);
      var s62 := CallDataLoad(s61);
      var s63 := PushN(s62, 1, 0x20);
      var s64 := Dup(s63, 3);
      var s65 := PushN(s64, 2, 0x01a0);
      var s66 := Add(s65);
      var s67 := Add(s66);
      var s68 := MStore(s67);
      var s69 := PushN(s68, 1, 0x20);
      var s70 := Dup(s69, 2);
      var s71 := Add(s70);
      var s72 := Swap(s71, 1);
      var s73 := Pop(s72);
      var s74 := Dup(s73, 1);
      var s75 := PushN(s74, 2, 0x01a0);
      var s76 := MStore(s75);
      var s77 := PushN(s76, 2, 0x01a0);
      var s78 := Pop(s77);
      var s79 := Pop(s78);
      var s80 := PushN(s79, 1, 0x20);
      var s81 := PushN(s80, 2, 0x0260);
      var s82 := PushN(s81, 2, 0x01a0);
      var s83 := MLoad(s82);
      var s84 := PushN(s83, 2, 0x01c0);
      var s85 := PushN(s84, 1, 0x00);
      var s86 := PushN(s85, 1, 0x01);
      var s87 := PushN(s86, 2, 0x0100);
      var s88 := MLoad(s87);
      var s89 := PushN(s88, 1, 0x03);
      var s90 := Dup(s89, 2);
      var s91 := Lt(s90);
      var s92 := IsZero(s91);
      var s93 := PushN(s92, 2, 0x09fc);
      assert s93.stack[0] == 0x9fc;
      var s94 := JumpI(s93);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s93.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s94, gas - 1)
      else
        ExecuteFromCFGNode_s14(s94, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 14
    * Starting at 0x170
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x02);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := PushN(s6, 2, 0x0185);
      assert s7.stack[0] == 0x185;
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s8, gas - 1)
      else
        ExecuteFromCFGNode_s15(s8, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 15
    * Starting at 0x17b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 16
    * Segment Id for this node is: 16
    * Starting at 0x185
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x185 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x0198);
      assert s8.stack[0] == 0x198;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s9, gas - 1)
      else
        ExecuteFromCFGNode_s17(s9, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 17
    * Starting at 0x193
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x193 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x019a);
      assert s2.stack[0] == 0x19a;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s3, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 19
    * Starting at 0x19a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0120);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0120);
      var s25 := MLoad(s24);
      var s26 := Gt(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x01da);
      assert s28.stack[0] == 0x1da;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s20(s29, gas - 1)
      else
        ExecuteFromCFGNode_s19(s29, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 20
    * Starting at 0x1c0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x09fc);
      assert s17.stack[0] == 0x9fc;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s18, gas - 1)
      else
        ExecuteFromCFGNode_s20(s18, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 21
    * Starting at 0x1da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Add(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := Eq(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x00ae);
      assert s12.stack[0] == 0xae;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s13, gas - 1)
      else
        ExecuteFromCFGNode_s21(s13, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 22
    * Starting at 0x1ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 4, 0x4515cef3);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0140);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x44);
      var s15 := CallDataLoad(s14);
      var s16 := PushN(s15, 2, 0x0160);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x64);
      var s19 := CallDataLoad(s18);
      var s20 := PushN(s19, 2, 0x0180);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 1, 0x00);
      var s23 := SLoad(s22);
      var s24 := ExtCodeSize(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x09fc);
      assert s26.stack[0] == 0x9fc;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s27, gas - 1)
      else
        ExecuteFromCFGNode_s22(s27, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 23
    * Starting at 0x21a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 2, 0x011c);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := SLoad(s6);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x0238);
      assert s10.stack[0] == 0x238;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s11, gas - 1)
      else
        ExecuteFromCFGNode_s23(s11, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 24
    * Starting at 0x22e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 24
    * Segment Id for this node is: 25
    * Starting at 0x238
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x238 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := SLoad(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 4, 0x70a08231);
      var s7 := PushN(s6, 2, 0x0140);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := PushN(s9, 2, 0x0160);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := PushN(s13, 1, 0x24);
      var s15 := PushN(s14, 2, 0x015c);
      var s16 := PushN(s15, 2, 0x0100);
      var s17 := MLoad(s16);
      var s18 := Gas(s17);
      var s19 := StaticCall(s18);
      var s20 := PushN(s19, 2, 0x026c);
      assert s20.stack[0] == 0x26c;
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s21, gas - 1)
      else
        ExecuteFromCFGNode_s25(s21, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 26
    * Starting at 0x262
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x262 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 26
    * Segment Id for this node is: 27
    * Starting at 0x26c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 28
    * Starting at 0x276
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x276 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s10 := PushN(s9, 2, 0x01a0);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x0180);
      var s13 := PushN(s12, 1, 0x04);
      var s14 := Dup(s13, 1);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 2, 0x01c0);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Dup(s19, 3);
      var s21 := PushN(s20, 1, 0x20);
      var s22 := Dup(s21, 6);
      var s23 := Add(s22);
      var s24 := PushN(s23, 1, 0x04);
      var s25 := Gas(s24);
      var s26 := StaticCall(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup(s28, 1);
      var s30 := MLoad(s29);
      var s31 := Dup(s30, 3);
      var s32 := Add(s31);
      var s33 := Swap(s32, 2);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := PushN(s35, 1, 0xe0);
      var s37 := MLoad(s36);
      var s38 := PushN(s37, 1, 0x20);
      var s39 := Dup(s38, 3);
      var s40 := PushN(s39, 2, 0x01c0);
      var s41 := Add(s40);
      var s42 := Add(s41);
      var s43 := MStore(s42);
      var s44 := PushN(s43, 1, 0x20);
      var s45 := Dup(s44, 2);
      var s46 := Add(s45);
      var s47 := Swap(s46, 1);
      var s48 := Pop(s47);
      var s49 := PushN(s48, 2, 0x0120);
      var s50 := MLoad(s49);
      var s51 := PushN(s50, 1, 0x20);
      var s52 := Dup(s51, 3);
      var s53 := PushN(s52, 2, 0x01c0);
      var s54 := Add(s53);
      var s55 := Add(s54);
      var s56 := MStore(s55);
      var s57 := PushN(s56, 1, 0x20);
      var s58 := Dup(s57, 2);
      var s59 := Add(s58);
      var s60 := Swap(s59, 1);
      var s61 := Pop(s60);
      var s62 := Dup(s61, 1);
      var s63 := PushN(s62, 2, 0x01c0);
      var s64 := MStore(s63);
      var s65 := PushN(s64, 2, 0x01c0);
      var s66 := Pop(s65);
      var s67 := Pop(s66);
      var s68 := PushN(s67, 1, 0x20);
      var s69 := PushN(s68, 2, 0x0260);
      var s70 := PushN(s69, 2, 0x01c0);
      var s71 := MLoad(s70);
      var s72 := PushN(s71, 2, 0x01e0);
      var s73 := PushN(s72, 1, 0x00);
      var s74 := PushN(s73, 2, 0x0100);
      var s75 := MLoad(s74);
      var s76 := Gas(s75);
      var s77 := Call(s76);
      var s78 := PushN(s77, 2, 0x031c);
      assert s78.stack[0] == 0x31c;
      var s79 := JumpI(s78);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s78.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s79, gas - 1)
      else
        ExecuteFromCFGNode_s28(s79, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 29
    * Starting at 0x312
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x312 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 29
    * Segment Id for this node is: 30
    * Starting at 0x31c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x032f);
      assert s8.stack[0] == 0x32f;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s9, gas - 1)
      else
        ExecuteFromCFGNode_s30(s9, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 31
    * Starting at 0x32a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0331);
      assert s2.stack[0] == 0x331;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s3, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 33
    * Starting at 0x331
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0140);
      var s25 := MLoad(s24);
      var s26 := Gt(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x0371);
      assert s28.stack[0] == 0x371;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s29, gas - 1)
      else
        ExecuteFromCFGNode_s32(s29, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 34
    * Starting at 0x357
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x09fc);
      assert s17.stack[0] == 0x9fc;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s18, gas - 1)
      else
        ExecuteFromCFGNode_s33(s18, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 35
    * Starting at 0x371
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x371 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0120);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0180);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x20);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 34
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 35
    * Segment Id for this node is: 32
    * Starting at 0x32f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s31(s2, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 37
    * Segment Id for this node is: 18
    * Starting at 0x198
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s18(s2, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 39
    * Segment Id for this node is: 4
    * Starting at 0x2b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x75b96abc);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0380);
      assert s5.stack[0] == 0x380;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s6, gas - 1)
      else
        ExecuteFromCFGNode_s40(s6, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 5
    * Starting at 0x37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x84);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s7, gas - 1)
      else
        ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 6
    * Starting at 0x42
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s7(s2, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 43
    * Segment Id for this node is: 36
    * Starting at 0x380
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x380 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xecb586a5);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0394);
      assert s5.stack[0] == 0x394;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s6, gas - 1)
      else
        ExecuteFromCFGNode_s44(s6, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 37
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x03ae);
      assert s4.stack[0] == 0x3ae;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s5, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 41
    * Starting at 0x3ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := PushN(s2, 2, 0x09fc);
      assert s3.stack[0] == 0x9fc;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s4, gas - 1)
      else
        ExecuteFromCFGNode_s46(s4, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 42
    * Starting at 0x3b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x23b872dd);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := MStore(s2);
      var s4 := Caller(s3);
      var s5 := PushN(s4, 2, 0x0120);
      var s6 := MStore(s5);
      var s7 := Address(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0160);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x20);
      var s15 := PushN(s14, 2, 0x0100);
      var s16 := PushN(s15, 1, 0x64);
      var s17 := PushN(s16, 2, 0x011c);
      var s18 := PushN(s17, 1, 0x00);
      var s19 := PushN(s18, 1, 0x01);
      var s20 := SLoad(s19);
      var s21 := Gas(s20);
      var s22 := Call(s21);
      var s23 := PushN(s22, 2, 0x03ed);
      assert s23.stack[0] == 0x3ed;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s24, gas - 1)
      else
        ExecuteFromCFGNode_s47(s24, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 43
    * Starting at 0x3e3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 48
    * Segment Id for this node is: 44
    * Starting at 0x3ed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s49(s7, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 45
    * Starting at 0x3f7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 4, 0xecb586a5);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0140);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x44);
      var s15 := CallDataLoad(s14);
      var s16 := PushN(s15, 2, 0x0160);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x64);
      var s19 := CallDataLoad(s18);
      var s20 := PushN(s19, 2, 0x0180);
      var s21 := MStore(s20);
      var s22 := PushN(s21, 1, 0x00);
      var s23 := SLoad(s22);
      var s24 := ExtCodeSize(s23);
      var s25 := IsZero(s24);
      var s26 := PushN(s25, 2, 0x09fc);
      assert s26.stack[0] == 0x9fc;
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s27, gas - 1)
      else
        ExecuteFromCFGNode_s50(s27, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 46
    * Starting at 0x429
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x429 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x84);
      var s4 := PushN(s3, 2, 0x011c);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := SLoad(s6);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x0447);
      assert s10.stack[0] == 0x447;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s11, gas - 1)
      else
        ExecuteFromCFGNode_s51(s11, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 47
    * Starting at 0x43d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 52
    * Segment Id for this node is: 48
    * Starting at 0x447
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x447 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x60);
      var s3 := CallDataSize(s2);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := CallDataCopy(s4);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x02);
      var s9 := Dup(s8, 2);
      var s10 := Dup(s9, 4);
      var s11 := MStore(s10);
      var s12 := Add(s11);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s53(s12, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 49
    * Starting at 0x45a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 2);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x09fc);
      assert s9.stack[0] == 0x9fc;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s10, gas - 1)
      else
        ExecuteFromCFGNode_s54(s10, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 50
    * Starting at 0x46a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x02);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x0180);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 4, 0x70a08231);
      var s8 := PushN(s7, 2, 0x01a0);
      var s9 := MStore(s8);
      var s10 := Address(s9);
      var s11 := PushN(s10, 2, 0x01c0);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x20);
      var s14 := PushN(s13, 2, 0x01a0);
      var s15 := PushN(s14, 1, 0x24);
      var s16 := PushN(s15, 2, 0x01bc);
      var s17 := PushN(s16, 2, 0x0180);
      var s18 := MLoad(s17);
      var s19 := Gas(s18);
      var s20 := StaticCall(s19);
      var s21 := PushN(s20, 2, 0x049f);
      assert s21.stack[0] == 0x49f;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s22, gas - 1)
      else
        ExecuteFromCFGNode_s55(s22, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 51
    * Starting at 0x495
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x495 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 56
    * Segment Id for this node is: 52
    * Starting at 0x49f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s7, gas - 1)
      else
        ExecuteFromCFGNode_s57(s7, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 53
    * Starting at 0x4a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01a0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0100);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 1, 0x03);
      var s7 := Dup(s6, 2);
      var s8 := Lt(s7);
      var s9 := IsZero(s8);
      var s10 := PushN(s9, 2, 0x09fc);
      assert s10.stack[0] == 0x9fc;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s11, gas - 1)
      else
        ExecuteFromCFGNode_s58(s11, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 54
    * Starting at 0x4bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := PushN(s6, 2, 0x01e0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s10 := PushN(s9, 2, 0x0200);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 2, 0x01e0);
      var s13 := PushN(s12, 1, 0x04);
      var s14 := Dup(s13, 1);
      var s15 := PushN(s14, 1, 0x20);
      var s16 := Dup(s15, 5);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := Add(s17);
      var s19 := Add(s18);
      var s20 := Dup(s19, 3);
      var s21 := PushN(s20, 1, 0x20);
      var s22 := Dup(s21, 6);
      var s23 := Add(s22);
      var s24 := PushN(s23, 1, 0x04);
      var s25 := Gas(s24);
      var s26 := StaticCall(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Dup(s28, 1);
      var s30 := MLoad(s29);
      var s31 := Dup(s30, 3);
      var s32 := Add(s31);
      var s33 := Swap(s32, 2);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := PushN(s35, 1, 0xe0);
      var s37 := MLoad(s36);
      var s38 := PushN(s37, 1, 0x20);
      var s39 := Dup(s38, 3);
      var s40 := PushN(s39, 2, 0x0220);
      var s41 := Add(s40);
      var s42 := Add(s41);
      var s43 := MStore(s42);
      var s44 := PushN(s43, 1, 0x20);
      var s45 := Dup(s44, 2);
      var s46 := Add(s45);
      var s47 := Swap(s46, 1);
      var s48 := Pop(s47);
      var s49 := PushN(s48, 2, 0x0100);
      var s50 := PushN(s49, 2, 0x0160);
      var s51 := MLoad(s50);
      var s52 := PushN(s51, 1, 0x03);
      var s53 := Dup(s52, 2);
      var s54 := Lt(s53);
      var s55 := IsZero(s54);
      var s56 := PushN(s55, 2, 0x09fc);
      assert s56.stack[0] == 0x9fc;
      var s57 := JumpI(s56);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s56.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s57, gas - 1)
      else
        ExecuteFromCFGNode_s59(s57, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 55
    * Starting at 0x531
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x531 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x20);
      var s2 := Mul(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := Dup(s5, 3);
      var s7 := PushN(s6, 2, 0x0220);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := PushN(s10, 1, 0x20);
      var s12 := Dup(s11, 2);
      var s13 := Add(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := Dup(s15, 1);
      var s17 := PushN(s16, 2, 0x0220);
      var s18 := MStore(s17);
      var s19 := PushN(s18, 2, 0x0220);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := PushN(s21, 1, 0x20);
      var s23 := PushN(s22, 2, 0x02c0);
      var s24 := PushN(s23, 2, 0x0220);
      var s25 := MLoad(s24);
      var s26 := PushN(s25, 2, 0x0240);
      var s27 := PushN(s26, 1, 0x00);
      var s28 := PushN(s27, 2, 0x0180);
      var s29 := MLoad(s28);
      var s30 := Gas(s29);
      var s31 := Call(s30);
      var s32 := PushN(s31, 2, 0x0571);
      assert s32.stack[0] == 0x571;
      var s33 := JumpI(s32);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s32.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s33, gas - 1)
      else
        ExecuteFromCFGNode_s60(s33, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 56
    * Starting at 0x567
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x567 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 61
    * Segment Id for this node is: 57
    * Starting at 0x571
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x571 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x02a0);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x0584);
      assert s8.stack[0] == 0x584;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s9, gas - 1)
      else
        ExecuteFromCFGNode_s62(s9, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 58
    * Starting at 0x57f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x0586);
      assert s2.stack[0] == 0x586;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s3, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 60
    * Starting at 0x586
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x586 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x01a0);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x01a0);
      var s25 := MLoad(s24);
      var s26 := Gt(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x05c6);
      assert s28.stack[0] == 0x5c6;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s29, gas - 1)
      else
        ExecuteFromCFGNode_s64(s29, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 61
    * Starting at 0x5ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x01c0);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x01a0);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x09fc);
      assert s17.stack[0] == 0x9fc;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s18, gas - 1)
      else
        ExecuteFromCFGNode_s65(s18, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 62
    * Starting at 0x5c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 2);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 1, 0x01);
      var s5 := Add(s4);
      var s6 := Dup(s5, 1);
      var s7 := Dup(s6, 4);
      var s8 := MStore(s7);
      var s9 := Dup(s8, 2);
      var s10 := Eq(s9);
      var s11 := IsZero(s10);
      var s12 := PushN(s11, 2, 0x045a);
      assert s12.stack[0] == 0x45a;
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s13, gas - 1)
      else
        ExecuteFromCFGNode_s66(s13, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 63
    * Starting at 0x5d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 4, 0x70a08231);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := MStore(s4);
      var s6 := Address(s5);
      var s7 := PushN(s6, 2, 0x0180);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 1, 0x20);
      var s10 := PushN(s9, 2, 0x0160);
      var s11 := PushN(s10, 1, 0x24);
      var s12 := PushN(s11, 2, 0x017c);
      var s13 := PushN(s12, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s14 := Gas(s13);
      var s15 := StaticCall(s14);
      var s16 := PushN(s15, 2, 0x0615);
      assert s16.stack[0] == 0x615;
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s17, gas - 1)
      else
        ExecuteFromCFGNode_s67(s17, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 64
    * Starting at 0x60b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 68
    * Segment Id for this node is: 65
    * Starting at 0x615
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x615 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 66
    * Starting at 0x61f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 4, 0x2e1a7d4d);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 2, 0x0180);
      var s11 := MStore(s10);
      var s12 := PushN(s11, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s13 := ExtCodeSize(s12);
      var s14 := IsZero(s13);
      var s15 := PushN(s14, 2, 0x09fc);
      assert s15.stack[0] == 0x9fc;
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s16, gas - 1)
      else
        ExecuteFromCFGNode_s70(s16, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 67
    * Starting at 0x653
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x653 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := PushN(s3, 2, 0x017c);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s7 := Gas(s6);
      var s8 := Call(s7);
      var s9 := PushN(s8, 2, 0x0683);
      assert s9.stack[0] == 0x683;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s10, gas - 1)
      else
        ExecuteFromCFGNode_s71(s10, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 68
    * Starting at 0x679
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x679 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 72
    * Segment Id for this node is: 69
    * Starting at 0x683
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x683 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 2, 0x0160);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0160);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 2, 0x0160);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0180);
      var s12 := SelfBalance(s11);
      var s13 := PushN(s12, 1, 0xe0);
      var s14 := MLoad(s13);
      var s15 := Gas(s14);
      var s16 := Call(s15);
      var s17 := PushN(s16, 2, 0x06ad);
      assert s17.stack[0] == 0x6ad;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s18, gas - 1)
      else
        ExecuteFromCFGNode_s73(s18, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 70
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 74
    * Segment Id for this node is: 71
    * Starting at 0x6ad
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0160);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 2, 0x0120);
      var s7 := MLoad(s6);
      var s8 := PushN(s7, 2, 0x0180);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 2, 0x0140);
      var s11 := MLoad(s10);
      var s12 := PushN(s11, 2, 0x01a0);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x60);
      var s15 := PushN(s14, 2, 0x0160);
      var s16 := Return(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 75
    * Segment Id for this node is: 59
    * Starting at 0x584
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x584 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s63(s2, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 77
    * Segment Id for this node is: 116
    * Starting at 0x9fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := Dup(s2, 1);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 78
    * Segment Id for this node is: 38
    * Starting at 0x394
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x394 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x2da5dc21);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x06cc);
      assert s5.stack[0] == 0x6cc;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s6, gas - 1)
      else
        ExecuteFromCFGNode_s79(s6, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 39
    * Starting at 0x3a0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x84);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s7, gas - 1)
      else
        ExecuteFromCFGNode_s80(s7, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 40
    * Starting at 0x3ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s45(s2, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 72
    * Starting at 0x6cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xf1dc3cc9);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x06e0);
      assert s5.stack[0] == 0x6e0;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s6, gas - 1)
      else
        ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 73
    * Starting at 0x6d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := PushN(s1, 1, 0xe0);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x06fa);
      assert s4.stack[0] == 0x6fa;
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s5, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 77
    * Starting at 0x6fa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := PushN(s2, 2, 0x09fc);
      assert s3.stack[0] == 0x9fc;
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s4, gas - 1)
      else
        ExecuteFromCFGNode_s84(s4, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 78
    * Starting at 0x700
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x700 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x23b872dd);
      var s2 := PushN(s1, 2, 0x0100);
      var s3 := MStore(s2);
      var s4 := Caller(s3);
      var s5 := PushN(s4, 2, 0x0120);
      var s6 := MStore(s5);
      var s7 := Address(s6);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0160);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x20);
      var s15 := PushN(s14, 2, 0x0100);
      var s16 := PushN(s15, 1, 0x64);
      var s17 := PushN(s16, 2, 0x011c);
      var s18 := PushN(s17, 1, 0x00);
      var s19 := PushN(s18, 1, 0x01);
      var s20 := SLoad(s19);
      var s21 := Gas(s20);
      var s22 := Call(s21);
      var s23 := PushN(s22, 2, 0x0739);
      assert s23.stack[0] == 0x739;
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s24, gas - 1)
      else
        ExecuteFromCFGNode_s85(s24, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 79
    * Starting at 0x72f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 86
    * Segment Id for this node is: 80
    * Starting at 0x739
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s87(s7, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 81
    * Starting at 0x743
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x743 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0100);
      var s2 := Pop(s1);
      var s3 := PushN(s2, 4, 0xf1dc3cc9);
      var s4 := PushN(s3, 2, 0x0100);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x04);
      var s7 := CallDataLoad(s6);
      var s8 := PushN(s7, 2, 0x0120);
      var s9 := MStore(s8);
      var s10 := PushN(s9, 1, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := PushN(s11, 2, 0x0140);
      var s13 := MStore(s12);
      var s14 := PushN(s13, 1, 0x44);
      var s15 := CallDataLoad(s14);
      var s16 := PushN(s15, 2, 0x0160);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 1, 0x00);
      var s19 := SLoad(s18);
      var s20 := ExtCodeSize(s19);
      var s21 := IsZero(s20);
      var s22 := PushN(s21, 2, 0x09fc);
      assert s22.stack[0] == 0x9fc;
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s23, gas - 1)
      else
        ExecuteFromCFGNode_s88(s23, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 82
    * Starting at 0x76e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x64);
      var s4 := PushN(s3, 2, 0x011c);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := SLoad(s6);
      var s8 := Gas(s7);
      var s9 := Call(s8);
      var s10 := PushN(s9, 2, 0x078c);
      assert s10.stack[0] == 0x78c;
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s11, gas - 1)
      else
        ExecuteFromCFGNode_s89(s11, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 83
    * Starting at 0x782
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x782 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 90
    * Segment Id for this node is: 84
    * Starting at 0x78c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x01);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := PushN(s4, 1, 0x03);
      var s6 := Dup(s5, 2);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := PushN(s8, 2, 0x09fc);
      assert s9.stack[0] == 0x9fc;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s10, gas - 1)
      else
        ExecuteFromCFGNode_s91(s10, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 85
    * Starting at 0x79b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x02);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 2, 0x0100);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 4, 0x70a08231);
      var s8 := PushN(s7, 2, 0x0140);
      var s9 := MStore(s8);
      var s10 := Address(s9);
      var s11 := PushN(s10, 2, 0x0160);
      var s12 := MStore(s11);
      var s13 := PushN(s12, 1, 0x20);
      var s14 := PushN(s13, 2, 0x0140);
      var s15 := PushN(s14, 1, 0x24);
      var s16 := PushN(s15, 2, 0x015c);
      var s17 := PushN(s16, 2, 0x0100);
      var s18 := MLoad(s17);
      var s19 := Gas(s18);
      var s20 := StaticCall(s19);
      var s21 := PushN(s20, 2, 0x07d0);
      assert s21.stack[0] == 0x7d0;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s22, gas - 1)
      else
        ExecuteFromCFGNode_s92(s22, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 86
    * Starting at 0x7c6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 93
    * Segment Id for this node is: 87
    * Starting at 0x7d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x1f);
      var s3 := ReturnDataSize(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s7, gas - 1)
      else
        ExecuteFromCFGNode_s94(s7, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 88
    * Starting at 0x7da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0140);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0120);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x02);
      var s6 := PushN(s5, 1, 0x24);
      var s7 := CallDataLoad(s6);
      var s8 := Xor(s7);
      var s9 := PushN(s8, 2, 0x0876);
      assert s9.stack[0] == 0x876;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s10, gas - 1)
      else
        ExecuteFromCFGNode_s95(s10, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 89
    * Starting at 0x7ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 4, 0x2e1a7d4d);
      var s2 := PushN(s1, 2, 0x0140);
      var s3 := MStore(s2);
      var s4 := PushN(s3, 2, 0x0120);
      var s5 := MLoad(s4);
      var s6 := PushN(s5, 2, 0x0160);
      var s7 := MStore(s6);
      var s8 := PushN(s7, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s9 := ExtCodeSize(s8);
      var s10 := IsZero(s9);
      var s11 := PushN(s10, 2, 0x09fc);
      assert s11.stack[0] == 0x9fc;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s12, gas - 1)
      else
        ExecuteFromCFGNode_s96(s12, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 90
    * Starting at 0x818
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x818 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x24);
      var s4 := PushN(s3, 2, 0x015c);
      var s5 := PushN(s4, 1, 0x00);
      var s6 := PushN(s5, 20, 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2);
      var s7 := Gas(s6);
      var s8 := Call(s7);
      var s9 := PushN(s8, 2, 0x0848);
      assert s9.stack[0] == 0x848;
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s10, gas - 1)
      else
        ExecuteFromCFGNode_s97(s10, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 91
    * Starting at 0x83e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 98
    * Segment Id for this node is: 92
    * Starting at 0x848
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x848 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 2, 0x0140);
      var s6 := Pop(s5);
      var s7 := PushN(s6, 1, 0x00);
      var s8 := PushN(s7, 1, 0x00);
      var s9 := PushN(s8, 2, 0x0140);
      var s10 := MLoad(s9);
      var s11 := PushN(s10, 2, 0x0160);
      var s12 := SelfBalance(s11);
      var s13 := PushN(s12, 1, 0xe0);
      var s14 := MLoad(s13);
      var s15 := Gas(s14);
      var s16 := Call(s15);
      var s17 := PushN(s16, 2, 0x096a);
      assert s17.stack[0] == 0x96a;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s18, gas - 1)
      else
        ExecuteFromCFGNode_s99(s18, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 93
    * Starting at 0x868
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x868 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 100
    * Segment Id for this node is: 102
    * Starting at 0x96a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0120);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 2, 0x0140);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 1, 0x20);
      var s7 := PushN(s6, 2, 0x0140);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 101
    * Segment Id for this node is: 95
    * Starting at 0x876
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x876 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x04);
      var s4 := PushN(s3, 2, 0x0180);
      var s5 := MStore(s4);
      var s6 := PushN(s5, 32, 0xa9059cbb00000000000000000000000000000000000000000000000000000000);
      var s7 := PushN(s6, 2, 0x01a0);
      var s8 := MStore(s7);
      var s9 := PushN(s8, 2, 0x0180);
      var s10 := PushN(s9, 1, 0x04);
      var s11 := Dup(s10, 1);
      var s12 := PushN(s11, 1, 0x20);
      var s13 := Dup(s12, 5);
      var s14 := PushN(s13, 2, 0x01c0);
      var s15 := Add(s14);
      var s16 := Add(s15);
      var s17 := Dup(s16, 3);
      var s18 := PushN(s17, 1, 0x20);
      var s19 := Dup(s18, 6);
      var s20 := Add(s19);
      var s21 := PushN(s20, 1, 0x04);
      var s22 := Gas(s21);
      var s23 := StaticCall(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Dup(s25, 1);
      var s27 := MLoad(s26);
      var s28 := Dup(s27, 3);
      var s29 := Add(s28);
      var s30 := Swap(s29, 2);
      var s31 := Pop(s30);
      var s32 := Pop(s31);
      var s33 := PushN(s32, 1, 0xe0);
      var s34 := MLoad(s33);
      var s35 := PushN(s34, 1, 0x20);
      var s36 := Dup(s35, 3);
      var s37 := PushN(s36, 2, 0x01c0);
      var s38 := Add(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := PushN(s40, 1, 0x20);
      var s42 := Dup(s41, 2);
      var s43 := Add(s42);
      var s44 := Swap(s43, 1);
      var s45 := Pop(s44);
      var s46 := PushN(s45, 2, 0x0120);
      var s47 := MLoad(s46);
      var s48 := PushN(s47, 1, 0x20);
      var s49 := Dup(s48, 3);
      var s50 := PushN(s49, 2, 0x01c0);
      var s51 := Add(s50);
      var s52 := Add(s51);
      var s53 := MStore(s52);
      var s54 := PushN(s53, 1, 0x20);
      var s55 := Dup(s54, 2);
      var s56 := Add(s55);
      var s57 := Swap(s56, 1);
      var s58 := Pop(s57);
      var s59 := Dup(s58, 1);
      var s60 := PushN(s59, 2, 0x01c0);
      var s61 := MStore(s60);
      var s62 := PushN(s61, 2, 0x01c0);
      var s63 := Pop(s62);
      var s64 := Pop(s63);
      var s65 := PushN(s64, 1, 0x20);
      var s66 := PushN(s65, 2, 0x0260);
      var s67 := PushN(s66, 2, 0x01c0);
      var s68 := MLoad(s67);
      var s69 := PushN(s68, 2, 0x01e0);
      var s70 := PushN(s69, 1, 0x00);
      var s71 := PushN(s70, 2, 0x0100);
      var s72 := MLoad(s71);
      var s73 := Gas(s72);
      var s74 := Call(s73);
      var s75 := PushN(s74, 2, 0x0915);
      assert s75.stack[0] == 0x915;
      var s76 := JumpI(s75);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s75.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s76, gas - 1)
      else
        ExecuteFromCFGNode_s102(s76, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 96
    * Starting at 0x90b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := PushN(s1, 1, 0x00);
      var s3 := PushN(s2, 1, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := PushN(s5, 1, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 103
    * Segment Id for this node is: 97
    * Starting at 0x915
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x915 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 2, 0x0240);
      var s3 := PushN(s2, 1, 0x20);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup(s4, 1);
      var s6 := Dup(s5, 3);
      var s7 := Gt(s6);
      var s8 := PushN(s7, 2, 0x0928);
      assert s8.stack[0] == 0x928;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s9, gas - 1)
      else
        ExecuteFromCFGNode_s104(s9, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 98
    * Starting at 0x923
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x923 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup(s0, 2);
      var s2 := PushN(s1, 2, 0x092a);
      assert s2.stack[0] == 0x92a;
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s3, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 100
    * Starting at 0x92a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 1);
      var s3 := Pop(s2);
      var s4 := Swap(s3, 1);
      var s5 := Pop(s4);
      var s6 := Dup(s5, 2);
      var s7 := MStore(s6);
      var s8 := Dup(s7, 1);
      var s9 := MLoad(s8);
      var s10 := PushN(s9, 1, 0x20);
      var s11 := Add(s10);
      var s12 := Dup(s11, 1);
      var s13 := PushN(s12, 2, 0x0140);
      var s14 := Dup(s13, 3);
      var s15 := Dup(s14, 5);
      var s16 := PushN(s15, 1, 0x04);
      var s17 := Gas(s16);
      var s18 := StaticCall(s17);
      var s19 := Swap(s18, 1);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      var s22 := Pop(s21);
      var s23 := PushN(s22, 1, 0x00);
      var s24 := PushN(s23, 2, 0x0140);
      var s25 := MLoad(s24);
      var s26 := Gt(s25);
      var s27 := IsZero(s26);
      var s28 := PushN(s27, 2, 0x096a);
      assert s28.stack[0] == 0x96a;
      var s29 := JumpI(s28);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s28.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s29, gas - 1)
      else
        ExecuteFromCFGNode_s106(s29, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 101
    * Starting at 0x950
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x950 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 2, 0x0160);
      var s2 := MLoad(s1);
      var s3 := PushN(s2, 2, 0x0140);
      var s4 := MLoad(s3);
      var s5 := Dup(s4, 2);
      var s6 := Dup(s5, 2);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := Sub(s7);
      var s9 := PushN(s8, 1, 0x08);
      var s10 := Mul(s9);
      var s11 := Shr(s10);
      var s12 := Swap(s11, 1);
      var s13 := Pop(s12);
      var s14 := Swap(s13, 1);
      var s15 := Pop(s14);
      var s16 := IsZero(s15);
      var s17 := PushN(s16, 2, 0x09fc);
      assert s17.stack[0] == 0x9fc;
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s18, gas - 1)
      else
        ExecuteFromCFGNode_s100(s18, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 99
    * Starting at 0x928
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x928 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup(s1, 1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s105(s2, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 74
    * Starting at 0x6e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x0fbcee6e);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0979);
      assert s5.stack[0] == 0x979;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s6, gas - 1)
      else
        ExecuteFromCFGNode_s109(s6, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 75
    * Starting at 0x6ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := Dup(s2, 1);
      var s4 := PushN(s3, 1, 0xa0);
      var s5 := Shr(s4);
      var s6 := PushN(s5, 2, 0x09fc);
      assert s6.stack[0] == 0x9fc;
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s7, gas - 1)
      else
        ExecuteFromCFGNode_s110(s7, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 76
    * Starting at 0x6f7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0xe0);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s83(s2, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 103
    * Starting at 0x979
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x979 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0x16f0115b);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x0995);
      assert s5.stack[0] == 0x995;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s6, gas - 1)
      else
        ExecuteFromCFGNode_s112(s6, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 104
    * Starting at 0x985
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x985 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallValue(s0);
      var s2 := PushN(s1, 2, 0x09fc);
      assert s2.stack[0] == 0x9fc;
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s3, gas - 1)
      else
        ExecuteFromCFGNode_s113(s3, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 105
    * Starting at 0x98a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x00);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 114
    * Segment Id for this node is: 106
    * Starting at 0x995
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x995 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xfc0c546a);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x09b1);
      assert s5.stack[0] == 0x9b1;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s6, gas - 1)
      else
        ExecuteFromCFGNode_s115(s6, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 107
    * Starting at 0x9a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallValue(s0);
      var s2 := PushN(s1, 2, 0x09fc);
      assert s2.stack[0] == 0x9fc;
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s3, gas - 1)
      else
        ExecuteFromCFGNode_s116(s3, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 108
    * Starting at 0x9a6
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := SLoad(s1);
      var s3 := PushN(s2, 1, 0xe0);
      var s4 := MStore(s3);
      var s5 := PushN(s4, 1, 0x20);
      var s6 := PushN(s5, 1, 0xe0);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 117
    * Segment Id for this node is: 109
    * Starting at 0x9b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := PushN(s1, 4, 0xc6610657);
      var s3 := Dup(s2, 2);
      var s4 := Xor(s3);
      var s5 := PushN(s4, 2, 0x09dd);
      assert s5.stack[0] == 0x9dd;
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s6, gas - 1)
      else
        ExecuteFromCFGNode_s118(s6, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 110
    * Starting at 0x9bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallValue(s0);
      var s2 := PushN(s1, 2, 0x09fc);
      assert s2.stack[0] == 0x9fc;
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s3, gas - 1)
      else
        ExecuteFromCFGNode_s119(s3, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 111
    * Starting at 0x9c2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 1, 0x01);
      var s2 := PushN(s1, 1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := PushN(s3, 1, 0x03);
      var s5 := Dup(s4, 2);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := PushN(s7, 2, 0x09fc);
      assert s8.stack[0] == 0x9fc;
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s9, gas - 1)
      else
        ExecuteFromCFGNode_s120(s9, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 112
    * Starting at 0x9d0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Mul(s0);
      var s2 := PushN(s1, 1, 0x02);
      var s3 := Add(s2);
      var s4 := SLoad(s3);
      var s5 := PushN(s4, 1, 0xe0);
      var s6 := MStore(s5);
      var s7 := PushN(s6, 1, 0x20);
      var s8 := PushN(s7, 1, 0xe0);
      var s9 := Return(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 121
    * Segment Id for this node is: 113
    * Starting at 0x9dd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }
}
