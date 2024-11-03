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
      var s6 := Push2(s5, 0x003f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s7, gas - 1)
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
      var s6 := Push4(s5, 0x255f3154);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0043);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s9, gas - 1)
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
      var s2 := Push4(s1, 0x2f80df2a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00c8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s18(s5, gas - 1)
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
      var s2 := Push4(s1, 0x504c6ff4);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00dd);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 7
    * Segment Id for this node is: 15
    * Starting at 0xdd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f0);
      var s3 := Push2(s2, 0x00eb);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x03b8);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s7, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 39
    * Starting at 0x3b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xeb

    requires s0.stack[3] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xeb;
      assert s1.Peek(3) == 0xf0;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x03ca);
      assert s11.Peek(0) == 0x3ca;
      assert s11.Peek(7) == 0xeb;
      assert s11.Peek(8) == 0xf0;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s12, gas - 1)
      else
        ExecuteFromCFGNode_s9(s12, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 40
    * Starting at 0x3c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xeb

    requires s0.stack[6] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0xeb;
      assert s1.Peek(7) == 0xf0;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 41
    * Starting at 0x3ca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xeb

    requires s0.stack[6] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xeb;
      assert s1.Peek(6) == 0xf0;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Swap4(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap4(s10);
      assert s11.Peek(1) == 0xeb;
      assert s11.Peek(6) == 0xf0;
      var s12 := Pop(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Swap3(s14);
      var s16 := Add(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Pop(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s21, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 16
    * Starting at 0xeb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf0;
      var s2 := Push2(s1, 0x029f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s3, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 29
    * Starting at 0x29f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf0;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 12, 0xffffffffffffffffffffffff);
      var s5 := Not(s4);
      var s6 := Caller(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Shl(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup3(s10);
      assert s11.Peek(7) == 0xf0;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x34);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Dup5(s16);
      var s18 := Swap1(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x54);
      var s21 := Dup2(s20);
      assert s21.Peek(6) == 0xf0;
      var s22 := Add(s21);
      var s23 := Dup4(s22);
      var s24 := Swap1(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x74);
      var s27 := Dup2(s26);
      var s28 := Add(s27);
      var s29 := Dup3(s28);
      var s30 := Swap1(s29);
      var s31 := MStore(s30);
      assert s31.Peek(4) == 0xf0;
      var s32 := TimeStamp(s31);
      var s33 := Push1(s32, 0x94);
      var s34 := Dup3(s33);
      var s35 := Add(s34);
      var s36 := MStore(s35);
      var s37 := Push0(s36);
      var s38 := Swap1(s37);
      var s39 := Dup2(s38);
      var s40 := Swap1(s39);
      var s41 := Push1(s40, 0xb4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s13(s41, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 30
    * Starting at 0x2dc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(6) == 0xf0;
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
      assert s11.Peek(10) == 0xf0;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Dup3(s13);
      var s15 := MStore(s14);
      var s16 := Dup1(s15);
      var s17 := MLoad(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Swap2(s18);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(10) == 0xf0;
      var s22 := Keccak256(s21);
      var s23 := Push0(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Dup1(s26);
      var s28 := Dup4(s27);
      var s29 := MStore(s28);
      var s30 := Dup4(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(11) == 0xf0;
      var s32 := Keccak256(s31);
      var s33 := Dup1(s32);
      var s34 := SLoad(s33);
      var s35 := Push1(s34, 0x01);
      var s36 := Push1(s35, 0x01);
      var s37 := Push1(s36, 0xa0);
      var s38 := Shl(s37);
      var s39 := Sub(s38);
      var s40 := Not(s39);
      var s41 := And(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s14(s41, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 31
    * Starting at 0x30b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[11] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(12) == 0xf0;
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := Or(s3);
      var s5 := Dup3(s4);
      var s6 := SStore(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Dup12(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(13) == 0xf0;
      var s12 := SStore(s11);
      var s13 := Push1(s12, 0x02);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := Dup11(s15);
      var s17 := Swap1(s16);
      var s18 := SStore(s17);
      var s19 := Push1(s18, 0x03);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(12) == 0xf0;
      var s22 := Dup10(s21);
      var s23 := Swap1(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x04);
      var s26 := Dup3(s25);
      var s27 := Add(s26);
      var s28 := Dup1(s27);
      var s29 := SLoad(s28);
      var s30 := Push1(s29, 0xff);
      var s31 := Not(s30);
      assert s31.Peek(14) == 0xf0;
      var s32 := And(s31);
      var s33 := Swap1(s32);
      var s34 := SStore(s33);
      var s35 := Dup3(s34);
      var s36 := Dup7(s35);
      var s37 := MStore(s36);
      var s38 := Swap3(s37);
      var s39 := Dup6(s38);
      var s40 := Add(s39);
      var s41 := Dup11(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s15(s41, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 32
    * Starting at 0x339
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -12
    * Net Capacity Effect: +12
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x339 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0xf0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(12) == 0xf0;
      var s2 := MStore(s1);
      var s3 := Swap3(s2);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := Dup9(s5);
      var s7 := Swap1(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(10) == 0xf0;
      var s12 := Dup8(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Swap4(s14);
      var s16 := Pop(s15);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Push32(s18, 0xbd45d97bcbcf86e1da2167399021a4c15c482905990f7c367d4b7279b5db29b1);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x80);
      assert s21.Peek(10) == 0xf0;
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x40);
      var s24 := MLoad(s23);
      var s25 := Dup1(s24);
      var s26 := Swap2(s25);
      var s27 := Sub(s26);
      var s28 := Swap1(s27);
      var s29 := Log2(s28);
      var s30 := Pop(s29);
      var s31 := Swap5(s30);
      assert s31.Peek(0) == 0xf0;
      var s32 := Swap4(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Pop(s35);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s37, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 17
    * Starting at 0xf0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
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
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x00bf);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s10, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 11
    * Starting at 0xbf
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf as nat
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

  /** Node 18
    * Segment Id for this node is: 12
    * Starting at 0xc8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00db);
      var s3 := Push2(s2, 0x00d6);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0398);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s7, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 36
    * Starting at 0x398
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xd6

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd6;
      assert s1.Peek(3) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x03a9);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s11, gas - 1)
      else
        ExecuteFromCFGNode_s20(s11, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 37
    * Starting at 0x3a6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xd6

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0xd6;
      assert s1.Peek(6) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 21
    * Segment Id for this node is: 38
    * Starting at 0x3a9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xd6

    requires s0.stack[5] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd6;
      assert s1.Peek(5) == 0xdb;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Swap3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := CallDataLoad(s10);
      assert s11.Peek(1) == 0xd6;
      assert s11.Peek(4) == 0xdb;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s14, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 13
    * Starting at 0xd6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
      var s2 := Push2(s1, 0x00fe);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s3, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 18
    * Starting at 0xfe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0xdb;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := And(s19);
      var s21 := Caller(s20);
      assert s21.Peek(5) == 0xdb;
      var s22 := Eq(s21);
      var s23 := Push2(s22, 0x0175);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s24, gas - 1)
      else
        ExecuteFromCFGNode_s24(s24, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 19
    * Starting at 0x11d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdb;
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
      assert s11.Peek(6) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x23);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4f6e6c7920746865206f776e65722063616e2066756c66696c6c20746865206c);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xdb;
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x6f636b);
      var s24 := Push1(s23, 0xe8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s25(s31, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 20
    * Starting at 0x16c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xdb;
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

  /** Node 26
    * Segment Id for this node is: 21
    * Starting at 0x175
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb;
      var s2 := Push1(s1, 0x04);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := And(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x01c3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s10, gas - 1)
      else
        ExecuteFromCFGNode_s27(s10, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 22
    * Starting at 0x183
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x183 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdb;
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
      assert s11.Peek(6) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x16);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 22, 0x131bd8dac8185b1c9958591e48199d5b199a5b1b1959);
      var s19 := Push1(s18, 0x52);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0xdb;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x016c);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s28, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 23
    * Starting at 0x1c3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := TimeStamp(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0206);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s10, gas - 1)
      else
        ExecuteFromCFGNode_s29(s10, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 24
    * Starting at 0x1d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdb;
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
      assert s11.Peek(6) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0c);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 12, 0x131bd8dac8195e1c1a5c9959);
      var s19 := Push1(s18, 0xa2);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0xdb;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x016c);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s28, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 25
    * Starting at 0x206
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x206 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x0243);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s4, gas - 1)
      else
        ExecuteFromCFGNode_s31(s4, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 26
    * Starting at 0x20c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xdb;
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
      assert s11.Peek(6) == 0xdb;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x0d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := PushN(s17, 13, 0x24b73b30b634b210383937b7b3);
      var s19 := Push1(s18, 0x99);
      var s20 := Shl(s19);
      var s21 := Push1(s20, 0x44);
      assert s21.Peek(6) == 0xdb;
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x64);
      var s26 := Add(s25);
      var s27 := Push2(s26, 0x016c);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s28, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 27
    * Starting at 0x243
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x243 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb;
      var s2 := Push1(s1, 0x04);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0xff);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Or(s10);
      assert s11.Peek(5) == 0xdb;
      var s12 := Swap1(s11);
      var s13 := SStore(s12);
      var s14 := Dup1(s13);
      var s15 := SLoad(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := MLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      assert s21.Peek(7) == 0xdb;
      var s22 := Sub(s21);
      var s23 := Swap1(s22);
      var s24 := Swap2(s23);
      var s25 := And(s24);
      var s26 := Swap1(s25);
      var s27 := Push32(s26, 0xc807ca363b72b12030d0e58b02c3d6d5133bdf9b7e8e6cb3c55e61851f3b858f);
      var s28 := Swap1(s27);
      var s29 := Push2(s28, 0x0292);
      var s30 := Swap1(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(2) == 0x292;
      assert s31.Peek(8) == 0xdb;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Add(s34);
      var s36 := Swap1(s35);
      var s37 := Jump(s36);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s37, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 28
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0xdb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xdb;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Swap2(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Log2(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0xdb;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s12, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 14
    * Starting at 0xdb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb as nat
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

  /** Node 35
    * Segment Id for this node is: 7
    * Starting at 0x43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x008f);
      var s3 := Push2(s2, 0x0051);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0381);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s7, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 33
    * Starting at 0x381
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x381 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x51

    requires s0.stack[3] == 0x8f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x51;
      assert s1.Peek(3) == 0x8f;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0391);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s10, gas - 1)
      else
        ExecuteFromCFGNode_s37(s10, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 34
    * Starting at 0x38e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x51

    requires s0.stack[4] == 0x8f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x51;
      assert s1.Peek(5) == 0x8f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 38
    * Segment Id for this node is: 35
    * Starting at 0x391
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x391 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x51

    requires s0.stack[4] == 0x8f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x51;
      assert s1.Peek(4) == 0x8f;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s7, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 8
    * Starting at 0x51
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8f;
      var s2 := Push0(s1);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup2(s6);
      var s8 := Swap1(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x8f;
      var s12 := Keccak256(s11);
      var s13 := Dup1(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := SLoad(s17);
      var s19 := Push1(s18, 0x02);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x8f;
      var s22 := SLoad(s21);
      var s23 := Push1(s22, 0x03);
      var s24 := Dup5(s23);
      var s25 := Add(s24);
      var s26 := SLoad(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Swap1(s27);
      var s29 := Swap5(s28);
      var s30 := Add(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(5) == 0x8f;
      var s32 := Push1(s31, 0x01);
      var s33 := Push1(s32, 0x01);
      var s34 := Push1(s33, 0xa0);
      var s35 := Shl(s34);
      var s36 := Sub(s35);
      var s37 := Swap1(s36);
      var s38 := Swap4(s37);
      var s39 := And(s38);
      var s40 := Swap5(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s41, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 9
    * Starting at 0x83
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x8f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      assert s1.Peek(2) == 0x8f;
      var s2 := Swap1(s1);
      var s3 := Swap3(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s11, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 10
    * Starting at 0x8f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Swap7(s10);
      var s12 := And(s11);
      var s13 := Dup7(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup7(s15);
      var s17 := Add(s16);
      var s18 := Swap5(s17);
      var s19 := Swap1(s18);
      var s20 := Swap5(s19);
      var s21 := MStore(s20);
      var s22 := Swap3(s21);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Swap2(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x60);
      var s30 := Dup4(s29);
      var s31 := Add(s30);
      var s32 := MStore(s31);
      var s33 := IsZero(s32);
      var s34 := IsZero(s33);
      var s35 := Push1(s34, 0x80);
      var s36 := Dup3(s35);
      var s37 := Add(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0xa0);
      var s40 := Add(s39);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s17(s40, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 6
    * Starting at 0x3f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f as nat
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
